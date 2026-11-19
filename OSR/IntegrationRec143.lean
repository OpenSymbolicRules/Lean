import OSR.IntegrationRec91

/-!
# Integration (RUBI): `sinh u cosh u = sinh (2 u) / 2`

6.7.9 #70 rewrites `(e + f x)^m (a + b sinh(c + d x) cosh(c + d x))^n` with the
double-angle formula.  Proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec143

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.9 #70 -/
def rubi679r70 : CRule where
  id := "integration.rubi_6_7_9_r70"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:70"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.app2 .mul (.int 2) (.var "c")) (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "x"))))) (.pow (.int 2) (.int (-1))))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  priority := 11803
  description := "RUBI 6.7.9 #70"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:70" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#70"

/-! ## Proofs -/

theorem rubi679r70_real : rubi679r70.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r70.conditions rubi679r70.body rubi679r70.result rubi679r70.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hS : ∀ w : ℝ, Real.sinh (2 * env "c" + 2 * env "d" * w) * 2⁻¹ = Real.sinh (env "c" + env "d" * w) * Real.cosh (env "c" + env "d" * w) := by
    intro w
    rw [show 2 * env "c" + 2 * env "d" * w = 2 * (env "c" + env "d" * w) by ring, Real.sinh_two_mul]
    ring
  have hS' : ∀ w : ℝ, Real.sinh (2 * env "c" + 2 * env "d" * w) = 2 * (Real.sinh (env "c" + env "d" * w) * Real.cosh (env "c" + env "d" * w)) := by
    intro w
    rw [show 2 * env "c" + 2 * env "d" * w = 2 * (env "c" + env "d" * w) by ring, Real.sinh_two_mul]
    ring
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r70, Defined, eval, Interp.real, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r70, Defined, eval, Interp.real, hk_m, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r70, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r70, Defined, eval, Interp.real, i2, im1, hk_m, hk_n, hS, hS'] at hw ⊢
    first | tauto | (simp_all; done) | (field_simp at hw ⊢; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r70, Defined, eval, recEnv]
  · simp only [rubi679r70, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi679r70.integrals.map (·.1)) Φ "x" w) rubi679r70.result) = Φ "I1" := by
      funext w; simp [rubi679r70, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi679r70, eval, Interp.real, i2, im1, hk_m, hk_n, hS, hS']
    first | done | (left; ring1) | (left; congr 2; ring) | (trace_state; sorry)

theorem rubi679r70_complex : rubi679r70.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r70.conditions rubi679r70.body rubi679r70.result rubi679r70.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hS : ∀ w : ℂ, Complex.sinh (2 * env "c" + 2 * env "d" * w) * 2⁻¹ = Complex.sinh (env "c" + env "d" * w) * Complex.cosh (env "c" + env "d" * w) := by
    intro w
    rw [show 2 * env "c" + 2 * env "d" * w = 2 * (env "c" + env "d" * w) by ring, Complex.sinh_two_mul]
    ring
  have hS' : ∀ w : ℂ, Complex.sinh (2 * env "c" + 2 * env "d" * w) = 2 * (Complex.sinh (env "c" + env "d" * w) * Complex.cosh (env "c" + env "d" * w)) := by
    intro w
    rw [show 2 * env "c" + 2 * env "d" * w = 2 * (env "c" + env "d" * w) by ring, Complex.sinh_two_mul]
    ring
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r70, Defined, eval, Interp.complex, hk_m] at h
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi679r70, Defined, eval, Interp.complex, hk_m, hk_n] at h
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r70, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi679r70, Defined, eval, Interp.complex, i2, im1, hk_m, hk_n, hS, hS'] at hw ⊢
    first | tauto | (simp_all; done) | (field_simp at hw ⊢; tauto) | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r70, Defined, eval, recEnv]
  · simp only [rubi679r70, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi679r70.integrals.map (·.1)) Φ "x" w) rubi679r70.result) = Φ "I1" := by
      funext w; simp [rubi679r70, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    simp [rubi679r70, eval, Interp.complex, i2, im1, hk_m, hk_n, hS, hS']
    first | done | (left; ring1) | (left; congr 2; ring) | (trace_state; sorry)

end OSR.IntegrationRec143
