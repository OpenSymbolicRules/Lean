import OSR.IntegrationRec91
import OSR.IntegrationRec138

/-!
# Integration (RUBI): `log(f + g x²) artanh(c x)/x` with `g = -c² f`

With `g = -c² f`, `log(f + g x²) = log f + log(1 - c x) + log(1 + c x)` wherever
the integrand is defined (there `f > 0` and `|c x| < 1`), and
`artanh u = (log(1 + u) - log(1 - u))/2`.  7.3.4 #136 and 7.3.1 #156 are
proved over ℝ (arctanh has no complex interpretation in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec145

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #136 -/
def rubi734r136 : CRule where
  id := "integration.rubi_7_3_4_r136"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:136"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))))) (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))) (.int 2)) (.pow (.var "x") (.int (-1))))),
    ("I3", (.app2 .mul (.pow (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int 2)) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "f", "g"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g")) (.int 0)]
  priority := 11808
  description := "RUBI 7.3.4 #136"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:136" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#136"

/-- RUBI 7.3.1 #156 -/
def rubi731r156 : CRule where
  id := "integration.rubi_7_3_1_r156"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:156"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))))) (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x")))) (.int 2)) (.pow (.var "x") (.int (-1))))),
    ("I3", (.app2 .mul (.pow (.app1 .ln (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int 2)) (.pow (.var "x") (.int (-1)))))]
  independent := ["c", "f", "g"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g")) (.int 0)]
  priority := 11809
  description := "RUBI 7.3.1 #156"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:156" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#156"

/-! ## Proofs -/

open OSR.IntegrationRec138

theorem rubi734r136_real : rubi734r136.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r136.conditions rubi734r136.body rubi734r136.result rubi734r136.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hg : env "g" = -(env "c" ^ 2 * env "f") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g")) (.int 0)) (by simp [rubi734r136])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  -- the facts at a point where the integrand is defined
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r136.body →
      0 < env "f" ∧ -1 < env "c" * w ∧ env "c" * w < 1 ∧ w ≠ 0 := by
    intro w hw
    simp [rubi734r136, Defined, eval, Interp.real, i2, im1] at hw
    first | (obtain ⟨⟨hA, hB, hC⟩, hD⟩ := hw; refine ⟨?_, hB, hC, hD⟩) | (trace_state; sorry)
    rw [hg] at hA
    have h1 : 0 < 1 - env "c" ^ 2 * w ^ 2 := by nlinarith
    have : 0 < env "f" * (1 - env "c" ^ 2 * w ^ 2) := by linarith
    exact pos_of_mul_pos_left this h1.le
  have hlog : ∀ w, 0 < env "f" → -1 < env "c" * w → env "c" * w < 1 →
      Real.log (env "f" + env "g" * w ^ 2) = Real.log (env "f") + Real.log (1 - env "c" * w) + Real.log (1 + env "c" * w) := by
    intro w hf h1 h2
    rw [show env "f" + env "g" * w ^ 2 = env "f" * ((1 - env "c" * w) * (1 + env "c" * w)) by rw [hg]; ring,
      Real.log_mul hf.ne' (by nlinarith), Real.log_mul (by linarith) (by linarith)]
    ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r136, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨hf, h1, h2, h0⟩ := hpt t hF.self_of_nhds
    filter_upwards [hF] with w hw
    obtain ⟨hf, h1, h2, h0⟩ := hpt w hw
    rcases hi with hi | hi | hi <;> subst hi <;> simp [rubi734r136, Defined, eval, Interp.real, i2, im1] <;>
      first | (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | assumption | linarith) | (refine ⟨?_, ?_⟩ <;> first | assumption | linarith) | (constructor <;> first | assumption | linarith) | linarith | assumption | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨hf, h1, h2, h0⟩ := hpt w hw
    simp [rubi734r136, Defined, eval, recEnv, Interp.real, i2, im1]
    first | (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | assumption | linarith | (rw [hg]; nlinarith [mul_pos hf (mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < 1 + env "c" * w))])) | (refine ⟨?_, ?_, ?_⟩ <;> first | assumption | linarith | (rw [hg]; nlinarith [mul_pos hf (mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < 1 + env "c" * w))])) | (trace_state; sorry)
  · simp only [rubi734r136, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    obtain ⟨hf, h1, h2, h0⟩ := hpt t hF.self_of_nhds
    have hev : (fun w => eval Interp.real (recEnv env (rubi734r136.integrals.map (·.1)) Φ "x" w) rubi734r136.result) =ᶠ[𝓝 t]
        fun w => Real.log (env "f") * Φ "I1" w - 1 / 2 * Φ "I2" w + 1 / 2 * Φ "I3" w := by
      filter_upwards [hF] with w hw
      obtain ⟨hf', h1', h2', h0'⟩ := hpt w hw
      simp [rubi734r136, eval, recEnv, Interp.real, i2, im1]
      first | (rw [hlog w hf' h1' h2']; ring_nf) | (trace_state; sorry)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine ((((hΦ1.const_mul (Real.log (env "f"))).sub (hΦ2.const_mul (1 / 2))).add (hΦ3.const_mul (1 / 2)))).congr_deriv ?_
    simp [rubi734r136, eval, Interp.real, i2, im1]
    first | (rw [hlog t hf h1 h2, artanh_split _ h1 h2]; ring_nf) | (trace_state; sorry)

theorem rubi731r156_real : rubi731r156.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r156.conditions rubi731r156.body rubi731r156.result rubi731r156.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hg : env "g" = -(env "c" ^ 2 * env "f") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g")) (.int 0)) (by simp [rubi731r156])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  -- the facts at a point where the integrand is defined
  have hpt : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r156.body →
      0 < env "f" ∧ -1 < env "c" * w ∧ env "c" * w < 1 ∧ w ≠ 0 := by
    intro w hw
    simp [rubi731r156, Defined, eval, Interp.real, i2, im1] at hw
    first | (obtain ⟨⟨hA, hB, hC⟩, hD⟩ := hw; refine ⟨?_, hB, hC, hD⟩) | (trace_state; sorry)
    rw [hg] at hA
    have h1 : 0 < 1 - env "c" ^ 2 * w ^ 2 := by nlinarith
    have : 0 < env "f" * (1 - env "c" ^ 2 * w ^ 2) := by linarith
    exact pos_of_mul_pos_left this h1.le
  have hlog : ∀ w, 0 < env "f" → -1 < env "c" * w → env "c" * w < 1 →
      Real.log (env "f" + env "g" * w ^ 2) = Real.log (env "f") + Real.log (1 - env "c" * w) + Real.log (1 + env "c" * w) := by
    intro w hf h1 h2
    rw [show env "f" + env "g" * w ^ 2 = env "f" * ((1 - env "c" * w) * (1 + env "c" * w)) by rw [hg]; ring,
      Real.log_mul hf.ne' (by nlinarith), Real.log_mul (by linarith) (by linarith)]
    ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r156, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨hf, h1, h2, h0⟩ := hpt t hF.self_of_nhds
    filter_upwards [hF] with w hw
    obtain ⟨hf, h1, h2, h0⟩ := hpt w hw
    rcases hi with hi | hi | hi <;> subst hi <;> simp [rubi731r156, Defined, eval, Interp.real, i2, im1] <;>
      first | (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | assumption | linarith) | (refine ⟨?_, ?_⟩ <;> first | assumption | linarith) | (constructor <;> first | assumption | linarith) | linarith | assumption | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    obtain ⟨hf, h1, h2, h0⟩ := hpt w hw
    simp [rubi731r156, Defined, eval, recEnv, Interp.real, i2, im1]
    first | (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | assumption | linarith | (rw [hg]; nlinarith [mul_pos hf (mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < 1 + env "c" * w))])) | (refine ⟨?_, ?_, ?_⟩ <;> first | assumption | linarith | (rw [hg]; nlinarith [mul_pos hf (mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < 1 + env "c" * w))])) | (trace_state; sorry)
  · simp only [rubi731r156, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2, hΦ3⟩ := hΦ
    obtain ⟨hf, h1, h2, h0⟩ := hpt t hF.self_of_nhds
    have hev : (fun w => eval Interp.real (recEnv env (rubi731r156.integrals.map (·.1)) Φ "x" w) rubi731r156.result) =ᶠ[𝓝 t]
        fun w => Real.log (env "f") * Φ "I1" w - 1 / 2 * Φ "I2" w + 1 / 2 * Φ "I3" w := by
      filter_upwards [hF] with w hw
      obtain ⟨hf', h1', h2', h0'⟩ := hpt w hw
      simp [rubi731r156, eval, recEnv, Interp.real, i2, im1]
      first | (rw [hlog w hf' h1' h2']; ring_nf) | (trace_state; sorry)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine ((((hΦ1.const_mul (Real.log (env "f"))).sub (hΦ2.const_mul (1 / 2))).add (hΦ3.const_mul (1 / 2)))).congr_deriv ?_
    simp [rubi731r156, eval, Interp.real, i2, im1]
    first | (rw [hlog t hf h1 h2, artanh_split _ h1 h2]; ring_nf) | (trace_state; sorry)

end OSR.IntegrationRec145
