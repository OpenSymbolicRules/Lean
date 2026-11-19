import OSR.IntegrationRec91

/-!
# Integration (RUBI): a locally constant factor `√(a + b x²)/√(d + e x²)`

With `b d = a e`, `(a + b x²)/(d + e x²)` is constant wherever both are positive,
so `√(a + b x²)/√(d + e x²)` is locally constant and can be taken out of the
integral.  5.3.7 #23, 7.3.4 #23 and 7.3.7 #23 (miscellaneous) are proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec150

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.3.7 #23 -/
def rubi537r23 : CRule where
  id := "integration.rubi_5_3_7_r23"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)]
  priority := 11835
  description := "RUBI 5.3.7 #23"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:23" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#23"

/-- RUBI 7.3.4 #23 -/
def rubi734mr23 : CRule where
  id := "integration.rubi_7_3_4_misc_r23"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2)),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)]
  priority := 11836
  description := "RUBI 7.3.4 #23"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:23" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#23"

/-- RUBI 7.3.7 #23 -/
def rubi737r23 : CRule where
  id := "integration.rubi_7_3_7_r23"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2)),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)]
  priority := 11837
  description := "RUBI 7.3.7 #23"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:23" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#23"

/-! ## Proofs -/

theorem rubi537r23_real : rubi537r23.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r23.conditions rubi537r23.body rubi537r23.result rubi537r23.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi537r23, Defined, eval, Interp.real, hk_m] at h
  have hbd : env "b" * env "d" = env "a" * env "e" := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)) (by simp [rubi537r23])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi537r23.body →
      0 < env "a" + env "b" * w ^ 2 ∧ 0 < env "d" + env "e" * w ^ 2 := by
    intro w hw
    simp [rubi537r23, Defined, eval, Interp.real, i2, im1, hk_m] at hw
    have k1 : Real.sqrt (env "a" + env "b" * w ^ 2) ≠ 0 := by tauto
    have k2 : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact ⟨Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k1)),
      Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k2))⟩
  have hK : ∀ w, 0 < env "a" + env "b" * w ^ 2 → 0 < env "d" + env "e" * w ^ 2 → 0 < env "a" + env "b" * t ^ 2 → 0 < env "d" + env "e" * t ^ 2 →
      Real.sqrt (env "a" + env "b" * w ^ 2) * (Real.sqrt (env "d" + env "e" * w ^ 2))⁻¹ = Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
    intro w h1 h2 h3 h4
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← Real.sqrt_div' _ h2.le, ← Real.sqrt_div' _ h4.le]
    congr 1
    rw [div_eq_div_iff h2.ne' h4.ne']
    linear_combination (w ^ 2 - t ^ 2) * hbd
  obtain ⟨hA0, hD0⟩ := hpt t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi537r23, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi537r23, Defined, eval, Interp.real, i2, im1, hk_m] at hw ⊢
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hpt w hw
    simp [rubi537r23, Defined, eval, recEnv, Interp.real, i2, im1, hk_m]
    first | exact ⟨h1.le, h2.le, (Real.sqrt_pos.2 h2).ne'⟩ | (trace_state; sorry)
  · simp only [rubi537r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hev : (fun w => eval Interp.real (recEnv env (rubi537r23.integrals.map (·.1)) Φ "x" w) rubi537r23.result) =ᶠ[𝓝 t]
        fun w => Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ * Φ "I1" w := by
      filter_upwards [hF] with w hw
      obtain ⟨h1, h2⟩ := hpt w hw
      simp [rubi537r23, eval, recEnv, Interp.real, i2, im1]
      first | exact Or.inl rfl | (left; exact hK w h1 h2 hA0 hD0) | (rw [hK w h1 h2 hA0 hD0]) | (trace_state; sorry)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [rubi537r23, eval, Interp.real, i2, im1, hk_m]
    have hsA : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hA0).ne'
    have hsD : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hD0).ne'
    first | (field_simp) | (trace_state; sorry)

theorem rubi734mr23_real : rubi734mr23.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr23.conditions rubi734mr23.body rubi734mr23.result rubi734mr23.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi734mr23, Defined, eval, Interp.real, hk_m] at h
  have hbd : env "b" * env "d" = env "a" * env "e" := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)) (by simp [rubi734mr23])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734mr23.body →
      0 < env "a" + env "b" * w ^ 2 ∧ 0 < env "d" + env "e" * w ^ 2 := by
    intro w hw
    simp [rubi734mr23, Defined, eval, Interp.real, i2, im1, hk_m] at hw
    have k1 : Real.sqrt (env "a" + env "b" * w ^ 2) ≠ 0 := by tauto
    have k2 : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact ⟨Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k1)),
      Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k2))⟩
  have hK : ∀ w, 0 < env "a" + env "b" * w ^ 2 → 0 < env "d" + env "e" * w ^ 2 → 0 < env "a" + env "b" * t ^ 2 → 0 < env "d" + env "e" * t ^ 2 →
      Real.sqrt (env "a" + env "b" * w ^ 2) * (Real.sqrt (env "d" + env "e" * w ^ 2))⁻¹ = Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
    intro w h1 h2 h3 h4
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← Real.sqrt_div' _ h2.le, ← Real.sqrt_div' _ h4.le]
    congr 1
    rw [div_eq_div_iff h2.ne' h4.ne']
    linear_combination (w ^ 2 - t ^ 2) * hbd
  obtain ⟨hA0, hD0⟩ := hpt t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr23, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi734mr23, Defined, eval, Interp.real, i2, im1, hk_m] at hw ⊢
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hpt w hw
    simp [rubi734mr23, Defined, eval, recEnv, Interp.real, i2, im1, hk_m]
    first | exact ⟨h1.le, h2.le, (Real.sqrt_pos.2 h2).ne'⟩ | (trace_state; sorry)
  · simp only [rubi734mr23, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hev : (fun w => eval Interp.real (recEnv env (rubi734mr23.integrals.map (·.1)) Φ "x" w) rubi734mr23.result) =ᶠ[𝓝 t]
        fun w => Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ * Φ "I1" w := by
      filter_upwards [hF] with w hw
      obtain ⟨h1, h2⟩ := hpt w hw
      simp [rubi734mr23, eval, recEnv, Interp.real, i2, im1]
      first | exact Or.inl rfl | (left; exact hK w h1 h2 hA0 hD0) | (rw [hK w h1 h2 hA0 hD0]) | (trace_state; sorry)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [rubi734mr23, eval, Interp.real, i2, im1, hk_m]
    have hsA : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hA0).ne'
    have hsD : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hD0).ne'
    first | (field_simp) | (trace_state; sorry)

theorem rubi737r23_real : rubi737r23.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r23.conditions rubi737r23.body rubi737r23.result rubi737r23.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi737r23, Defined, eval, Interp.real, hk_m] at h
  have hbd : env "b" * env "d" = env "a" * env "e" := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "e"))) (.int 0)) (by simp [rubi737r23])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r23.body →
      0 < env "a" + env "b" * w ^ 2 ∧ 0 < env "d" + env "e" * w ^ 2 := by
    intro w hw
    simp [rubi737r23, Defined, eval, Interp.real, i2, im1, hk_m] at hw
    have k1 : Real.sqrt (env "a" + env "b" * w ^ 2) ≠ 0 := by tauto
    have k2 : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    exact ⟨Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k1)),
      Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm k2))⟩
  have hK : ∀ w, 0 < env "a" + env "b" * w ^ 2 → 0 < env "d" + env "e" * w ^ 2 → 0 < env "a" + env "b" * t ^ 2 → 0 < env "d" + env "e" * t ^ 2 →
      Real.sqrt (env "a" + env "b" * w ^ 2) * (Real.sqrt (env "d" + env "e" * w ^ 2))⁻¹ = Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
    intro w h1 h2 h3 h4
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← Real.sqrt_div' _ h2.le, ← Real.sqrt_div' _ h4.le]
    congr 1
    rw [div_eq_div_iff h2.ne' h4.ne']
    linear_combination (w ^ 2 - t ^ 2) * hbd
  obtain ⟨hA0, hD0⟩ := hpt t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r23, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi737r23, Defined, eval, Interp.real, i2, im1, hk_m] at hw ⊢
    first | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨h1, h2⟩ := hpt w hw
    simp [rubi737r23, Defined, eval, recEnv, Interp.real, i2, im1, hk_m]
    first | exact ⟨h1.le, h2.le, (Real.sqrt_pos.2 h2).ne'⟩ | (trace_state; sorry)
  · simp only [rubi737r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hev : (fun w => eval Interp.real (recEnv env (rubi737r23.integrals.map (·.1)) Φ "x" w) rubi737r23.result) =ᶠ[𝓝 t]
        fun w => Real.sqrt (env "a" + env "b" * t ^ 2) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ * Φ "I1" w := by
      filter_upwards [hF] with w hw
      obtain ⟨h1, h2⟩ := hpt w hw
      simp [rubi737r23, eval, recEnv, Interp.real, i2, im1]
      first | exact Or.inl rfl | (left; exact hK w h1 h2 hA0 hD0) | (rw [hK w h1 h2 hA0 hD0]) | (trace_state; sorry)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine (hΦ.const_mul _).congr_deriv ?_
    simp [rubi737r23, eval, Interp.real, i2, im1, hk_m]
    have hsA : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hA0).ne'
    have hsD : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hD0).ne'
    first | (field_simp) | (trace_state; sorry)

end OSR.IntegrationRec150
