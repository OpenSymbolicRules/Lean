import OSR.IntegrationRec131

/-!
# Integration (RUBI): integration by parts of `A(c x/√(a + b x²))`

For `A = artanh` with `b = c²` and `A = arctan` with `b = -c²`:
`x A'(u) u' = c x/√(a + b x²)`, a field identity in `q = √(a + b x²)`.
Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec135

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #13 -/
def rubi734mr13 : CRule where
  id := "integration.rubi_7_3_4_misc_r13"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:13"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2))]
  priority := 11101
  description := "RUBI 7.3.4 #13"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:13" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#13"

/-- RUBI 7.3.7 #13 -/
def rubi737r13 : CRule where
  id := "integration.rubi_7_3_7_r13"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:13"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2))]
  priority := 11102
  description := "RUBI 7.3.7 #13"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:13" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#13"

/-- RUBI 5.3.7 #13 -/
def rubi537r13 : CRule where
  id := "integration.rubi_5_3_7_r13"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:13"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.var "x") (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)]
  priority := 11103
  description := "RUBI 5.3.7 #13"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:13" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#13"

/-! ## Proofs -/

theorem rubi734mr13_real : rubi734mr13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734mr13.conditions rubi734mr13.body rubi734mr13.result rubi734mr13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hb : env "b" = env "c" ^ 2 := by
    have h := hc (.eq (.var "b") (.pow (.var "c") (.int 2))) (by simp [rubi734mr13])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734mr13.body → 0 < (env "a" + env "b" * w ^ 2) ∧ (-1 < (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) ∧ (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) < 1) := by
    intro w h
    simp [rubi734mr13, Defined, eval, Interp.real, i2, im1] at h
    first | exact ⟨lt_of_le_of_ne h.1.1 (fun h0 => h.1.2 (by rw [← h0, Real.sqrt_zero])), h.2⟩ | exact ⟨lt_of_le_of_ne h.1 (fun h0 => h.2 (by rw [← h0, Real.sqrt_zero])), trivial⟩ | exact h | tauto | (trace_state; sorry)
  obtain ⟨hQ, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734mr13, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb' := (hBody w hw).1
    simp [Defined, eval, Interp.real, i2, im1, hb'.le, hb'.ne', Real.sqrt_ne_zero'.2 hb']
  · filter_upwards [hF] with w hw
    have hb' := hBody w hw
    simp [rubi734mr13, Defined, eval, recEnv, Interp.real, i2, im1, hb'.1.le, Real.sqrt_ne_zero'.2 hb'.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734mr13, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, i2, im1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734mr13.integrals.map (·.1)) Φ "x" w) rubi734mr13.result) =
        fun w => w * Real.artanh (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) + -1 * env "c" * Φ "I1" w := by
      funext w; simp [rubi734mr13, eval, recEnv, Interp.real, i2, im1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi734mr13.body = Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) := by
      simp [rubi734mr13, eval, Interp.real, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "a" + env "b" * w ^ 2)) (env "b" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "b")).const_add (env "a")
    have hq := (hQd.sqrt hQ.ne').inv (Real.sqrt_ne_zero'.2 hQ)
    have hq0 : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    have hu := (((hasDerivAt_id t).const_mul (env "c")).mul hq).congr_deriv
      (show _ = env "c" * ((Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ - env "b" * t ^ 2 * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ ^ 3) by
        simp only [id, mul_one, Pi.inv_apply, Pi.mul_apply]; field_simp; ring)
    have hA := (OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [id, one_mul, mul_one, Function.comp_def, Pi.inv_apply, Pi.mul_apply]
    have h1u : 1 - (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) ^ 2 ≠ 0 := by nlinarith [hd1, hd2]
    generalize Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) = AT
    generalize (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ = r at h1u ⊢
    have key : (1 - (env "c" * t * r) ^ 2)⁻¹ * (env "c" * (r - env "b" * t ^ 2 * r ^ 3)) = env "c" * r := by
      rw [hb]
      rw [show env "c" * (r - (env "c" ^ 2) * t ^ 2 * r ^ 3) = env "c" * r * (1 - (env "c" * t * r) ^ 2) by ring,
        mul_comm, mul_assoc, mul_inv_cancel₀ h1u, mul_one]
    rw [key]
    ring

theorem rubi737r13_real : rubi737r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi737r13.conditions rubi737r13.body rubi737r13.result rubi737r13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hb : env "b" = env "c" ^ 2 := by
    have h := hc (.eq (.var "b") (.pow (.var "c") (.int 2))) (by simp [rubi737r13])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi737r13.body → 0 < (env "a" + env "b" * w ^ 2) ∧ (-1 < (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) ∧ (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) < 1) := by
    intro w h
    simp [rubi737r13, Defined, eval, Interp.real, i2, im1] at h
    first | exact ⟨lt_of_le_of_ne h.1.1 (fun h0 => h.1.2 (by rw [← h0, Real.sqrt_zero])), h.2⟩ | exact ⟨lt_of_le_of_ne h.1 (fun h0 => h.2 (by rw [← h0, Real.sqrt_zero])), trivial⟩ | exact h | tauto | (trace_state; sorry)
  obtain ⟨hQ, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi737r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb' := (hBody w hw).1
    simp [Defined, eval, Interp.real, i2, im1, hb'.le, hb'.ne', Real.sqrt_ne_zero'.2 hb']
  · filter_upwards [hF] with w hw
    have hb' := hBody w hw
    simp [rubi737r13, Defined, eval, recEnv, Interp.real, i2, im1, hb'.1.le, Real.sqrt_ne_zero'.2 hb'.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi737r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, i2, im1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi737r13.integrals.map (·.1)) Φ "x" w) rubi737r13.result) =
        fun w => w * Real.artanh (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) + -1 * env "c" * Φ "I1" w := by
      funext w; simp [rubi737r13, eval, recEnv, Interp.real, i2, im1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi737r13.body = Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) := by
      simp [rubi737r13, eval, Interp.real, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "a" + env "b" * w ^ 2)) (env "b" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "b")).const_add (env "a")
    have hq := (hQd.sqrt hQ.ne').inv (Real.sqrt_ne_zero'.2 hQ)
    have hq0 : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    have hu := (((hasDerivAt_id t).const_mul (env "c")).mul hq).congr_deriv
      (show _ = env "c" * ((Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ - env "b" * t ^ 2 * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ ^ 3) by
        simp only [id, mul_one, Pi.inv_apply, Pi.mul_apply]; field_simp; ring)
    have hA := (OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [id, one_mul, mul_one, Function.comp_def, Pi.inv_apply, Pi.mul_apply]
    have h1u : 1 - (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) ^ 2 ≠ 0 := by nlinarith [hd1, hd2]
    generalize Real.artanh (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) = AT
    generalize (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ = r at h1u ⊢
    have key : (1 - (env "c" * t * r) ^ 2)⁻¹ * (env "c" * (r - env "b" * t ^ 2 * r ^ 3)) = env "c" * r := by
      rw [hb]
      rw [show env "c" * (r - (env "c" ^ 2) * t ^ 2 * r ^ 3) = env "c" * r * (1 - (env "c" * t * r) ^ 2) by ring,
        mul_comm, mul_assoc, mul_inv_cancel₀ h1u, mul_one]
    rw [key]
    ring

theorem rubi537r13_real : rubi537r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi537r13.conditions rubi537r13.body rubi537r13.result rubi537r13.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hb : env "b" = -env "c" ^ 2 := by
    have h := hc (.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)) (by simp [rubi537r13])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi537r13.body → 0 < (env "a" + env "b" * w ^ 2) ∧ True := by
    intro w h
    simp [rubi537r13, Defined, eval, Interp.real, i2, im1] at h
    first | exact ⟨lt_of_le_of_ne h.1.1 (fun h0 => h.1.2 (by rw [← h0, Real.sqrt_zero])), h.2⟩ | exact ⟨lt_of_le_of_ne h.1 (fun h0 => h.2 (by rw [← h0, Real.sqrt_zero])), trivial⟩ | exact h | tauto | (trace_state; sorry)
  obtain ⟨hQ, -⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi537r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb' := (hBody w hw).1
    simp [Defined, eval, Interp.real, i2, im1, hb'.le, hb'.ne', Real.sqrt_ne_zero'.2 hb']
  · filter_upwards [hF] with w hw
    have hb' := hBody w hw
    simp [rubi537r13, Defined, eval, recEnv, Interp.real, i2, im1, hb'.1.le, Real.sqrt_ne_zero'.2 hb'.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi537r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") (t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, i2, im1]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi537r13.integrals.map (·.1)) Φ "x" w) rubi537r13.result) =
        fun w => w * Real.arctan (env "c" * w * (Real.sqrt (env "a" + env "b" * w ^ 2))⁻¹) + -1 * env "c" * Φ "I1" w := by
      funext w; simp [rubi537r13, eval, recEnv, Interp.real, i2, im1]
    have hEF : eval Interp.real (Function.update env "x" t) rubi537r13.body = Real.arctan (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) := by
      simp [rubi537r13, eval, Interp.real, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "a" + env "b" * w ^ 2)) (env "b" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "b")).const_add (env "a")
    have hq := (hQd.sqrt hQ.ne').inv (Real.sqrt_ne_zero'.2 hQ)
    have hq0 : Real.sqrt (env "a" + env "b" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    have hu := (((hasDerivAt_id t).const_mul (env "c")).mul hq).congr_deriv
      (show _ = env "c" * ((Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ - env "b" * t ^ 2 * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ ^ 3) by
        simp only [id, mul_one, Pi.inv_apply, Pi.mul_apply]; field_simp; ring)
    have hA := (Real.hasDerivAt_arctan' _).comp t hu
    refine (((hasDerivAt_id t).mul hA).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [id, one_mul, mul_one, Function.comp_def, Pi.inv_apply, Pi.mul_apply]
    have h1u : 1 + (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) ^ 2 ≠ 0 := by positivity
    generalize Real.arctan (env "c" * t * (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹) = AT
    generalize (Real.sqrt (env "a" + env "b" * t ^ 2))⁻¹ = r at h1u ⊢
    have key : (1 + (env "c" * t * r) ^ 2)⁻¹ * (env "c" * (r - env "b" * t ^ 2 * r ^ 3)) = env "c" * r := by
      rw [hb]
      rw [show env "c" * (r - (-env "c" ^ 2) * t ^ 2 * r ^ 3) = env "c" * r * (1 + (env "c" * t * r) ^ 2) by ring,
        mul_comm, mul_assoc, mul_inv_cancel₀ h1u, mul_one]
    rw [key]
    ring


end OSR.IntegrationRec135
