import OSR.IntegrationRec91

/-!
# Integration (RUBI): integration by parts of arctan(tanh) and arctan(coth)

`(arctan ∘ tanh)(a + b x)' = b/(cosh² + sinh²) = b sech(2a + 2bx)`, and
`(arctan ∘ coth)(a + b x)' = -b sech(2a + 2bx)` (`cosh 2u = cosh² u + sinh² u`).
Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec134

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.3.7 #43 -/
def rubi537r43 : CRule where
  id := "integration.rubi_5_3_7_r43"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:43"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctan (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctan (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.app1 .sech (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b"]
  priority := 11001
  description := "RUBI 5.3.7 #43"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:43" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#43"

/-- RUBI 5.3.7 #45 -/
def rubi537r45 : CRule where
  id := "integration.rubi_5_3_7_r45"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:45"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctan (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctan (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app2 .mul (.var "b") (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.app1 .sech (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b"]
  priority := 11002
  description := "RUBI 5.3.7 #45"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:45" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#45"

/-! ## Proofs -/

/-- `d/dw tanh (a + b w) = b / cosh² (a + b w)`. -/
theorem hasDerivAt_tanh_lin (a b t : ℝ) :
    HasDerivAt (fun w => Real.tanh (a + b * w)) (b / Real.cosh (a + b * t) ^ 2) t := by
  have hl : HasDerivAt (fun w => a + b * w) b t := by
    simpa using ((hasDerivAt_id t).const_mul b).const_add a
  have hc : Real.cosh (a + b * t) ≠ 0 := (Real.cosh_pos _).ne'
  have h := ((Real.hasDerivAt_sinh (a + b * t)).div (Real.hasDerivAt_cosh (a + b * t)) hc).comp t hl
  have hf : (fun w => Real.tanh (a + b * w)) = (fun w => Real.sinh (a + b * w) / Real.cosh (a + b * w)) := by
    funext w; rw [Real.tanh_eq_sinh_div_cosh]
  rw [hf]
  refine h.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq (a + b * t)
  field_simp
  linear_combination b * hcs

/-- `d/dw coth (a + b w) = -b / sinh² (a + b w)` where `sinh (a + b w) ≠ 0`. -/
theorem hasDerivAt_coth_lin (a b t : ℝ) (hs : Real.sinh (a + b * t) ≠ 0) :
    HasDerivAt (fun w => Fn.coth (a + b * w)) (-b / Real.sinh (a + b * t) ^ 2) t := by
  have hl : HasDerivAt (fun w => a + b * w) b t := by
    simpa using ((hasDerivAt_id t).const_mul b).const_add a
  have h := ((Real.hasDerivAt_cosh (a + b * t)).div (Real.hasDerivAt_sinh (a + b * t)) hs).comp t hl
  have hev : (fun w => Real.cosh (a + b * w) / Real.sinh (a + b * w)) =ᶠ[𝓝 t] (fun w => Fn.coth (a + b * w)) := by
    have hcont : ContinuousAt (fun w => Real.sinh (a + b * w)) t := by fun_prop
    filter_upwards [hcont.eventually_ne hs] with w hw
    have hc : Real.cosh (a + b * w) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [Fn.coth, Real.tanh_eq_sinh_div_cosh]
    field_simp
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq (a + b * t)
  field_simp
  linear_combination -b * hcs

theorem rubi537r43_real : rubi537r43.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r43.conditions rubi537r43.body rubi537r43.result rubi537r43.integrals
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi537r43, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by simp [Defined, eval, Interp.real]
  · exact Eventually.of_forall fun w => by simp [rubi537r43, Defined, eval, recEnv, Interp.real]
  · simp only [rubi537r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (Real.cosh (2 * (env "a" + env "b" * t)))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, Fn.sech]
      left; ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi537r43.integrals.map (·.1)) Φ "x" w) rubi537r43.result) =
        fun w => w * Real.arctan (Real.tanh (env "a" + env "b" * w)) + -1 * env "b" * Φ "I1" w := by
      funext w; simp [rubi537r43, eval, recEnv, Interp.real]
    have hEF : eval Interp.real (Function.update env "x" t) rubi537r43.body =
        Real.arctan (Real.tanh (env "a" + env "b" * t)) := by
      simp [rubi537r43, eval, Interp.real]
    rw [hfun, hEF]
    have hA := (Real.hasDerivAt_arctan' _).comp t (hasDerivAt_tanh_lin (env "a") (env "b") t)
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [id, one_mul, Function.comp_def]
    rw [Real.cosh_two_mul, Real.tanh_eq_sinh_div_cosh]
    have hc : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
    have hcs : Real.cosh (env "a" + env "b" * t) ^ 2 + Real.sinh (env "a" + env "b" * t) ^ 2 ≠ 0 := by positivity
    generalize Real.arctan (Real.tanh (env "a" + env "b" * t)) = AT
    generalize Real.sinh (env "a" + env "b" * t) = S at hcs ⊢
    generalize Real.cosh (env "a" + env "b" * t) = C at hc hcs ⊢
    field_simp
    ring

theorem rubi537r45_real : rubi537r45.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r45.conditions rubi537r45.body rubi537r45.result rubi537r45.integrals
  intro env hc t hF
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi537r45.body →
      env "a" + env "b" * w ≠ 0 := by
    intro w h; simp [rubi537r45, Defined, eval, Interp.real] at h; exact h
  have hs : Real.sinh (env "a" + env "b" * t) ≠ 0 := fun h => hBody t hF.self_of_nhds (Real.sinh_eq_zero.1 h)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi537r45, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    exact Eventually.of_forall fun w => by simp [Defined, eval, Interp.real]
  · filter_upwards [hF] with w hw
    have := hBody w hw
    simp [rubi537r45, Defined, eval, recEnv, Interp.real, this]
  · simp only [rubi537r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (Real.cosh (2 * (env "a" + env "b" * t)))⁻¹) t := by
      convert hΦ using 1
      simp [eval, Interp.real, Fn.sech]
      left; ring_nf
    have hfun : (fun w => eval Interp.real (recEnv env (rubi537r45.integrals.map (·.1)) Φ "x" w) rubi537r45.result) =
        fun w => w * Real.arctan (Fn.coth (env "a" + env "b" * w)) + env "b" * Φ "I1" w := by
      funext w; simp [rubi537r45, eval, recEnv, Interp.real]
    have hEF : eval Interp.real (Function.update env "x" t) rubi537r45.body =
        Real.arctan (Fn.coth (env "a" + env "b" * t)) := by
      simp [rubi537r45, eval, Interp.real]
    rw [hfun, hEF]
    have hA := (Real.hasDerivAt_arctan' _).comp t (hasDerivAt_coth_lin (env "a") (env "b") t hs)
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [id, one_mul, Function.comp_def]
    have hct : Fn.coth (env "a" + env "b" * t) = Real.cosh (env "a" + env "b" * t) / Real.sinh (env "a" + env "b" * t) := by
      have hc : Real.cosh (env "a" + env "b" * t) ≠ 0 := (Real.cosh_pos _).ne'
      simp only [Fn.coth, Real.tanh_eq_sinh_div_cosh]; field_simp
    rw [Real.cosh_two_mul, hct]
    have hcs : Real.cosh (env "a" + env "b" * t) ^ 2 + Real.sinh (env "a" + env "b" * t) ^ 2 ≠ 0 := by positivity
    generalize Real.arctan (Real.cosh (env "a" + env "b" * t) / Real.sinh (env "a" + env "b" * t)) = AT
    generalize Real.sinh (env "a" + env "b" * t) = S at hs hcs ⊢
    generalize Real.cosh (env "a" + env "b" * t) = C at hcs ⊢
    field_simp
    ring

end OSR.IntegrationRec134
