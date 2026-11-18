import OSR.IntegrationRec131

/-!
# Integration (RUBI): integration by parts of `(d + e log(f + g x²)) (a + b A(c x))`

For `A = artanh` and `A = arctan`: the product rule on `x L M` leaves two terms,
`x L' M = 2 e g x² M/(f + g x²)` and `x L M' = b c x L/(1 ∓ c² x²)`, which are
the residual integrands.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec132

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #134 -/
def rubi734r134 : CRule where
  id := "integration.rubi_7_3_4_r134"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:134"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10801
  description := "RUBI 7.3.4 #134"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:134" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#134"

/-- RUBI 7.3.1 #154 -/
def rubi731r154 : CRule where
  id := "integration.rubi_7_3_1_r154"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:154"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10802
  description := "RUBI 7.3.1 #154"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:154" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#154"

/-- RUBI 5.3.4 #134 -/
def rubi534r134 : CRule where
  id := "integration.rubi_5_3_4_r134"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:134"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10803
  description := "RUBI 5.3.4 #134"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:134" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#134"

/-! ## Proofs -/

theorem rubi734r134_real : rubi734r134.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r134.conditions rubi734r134.body rubi734r134.result rubi734r134.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r134.body →
      0 < env "f" + env "g" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi734r134, Defined, eval, Interp.real, i2] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hP, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r134, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.1
      have hDw' : (1 - (env "c" * w) ^ 2) ≠ 0 := (by nlinarith [hb.2.1, hb.2.2])
      simp [Defined, eval, Interp.real, i2, im1, hb.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi734r134, Defined, eval, recEnv, Interp.real, i2, hb.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734r134, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ 2 * (env "a" + env "b" * Real.artanh (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1]
    have hΦ2' : HasDerivAt (Φ "I2") (t * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 - (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r134.integrals.map (·.1)) Φ "x" w) rubi734r134.result) =
        fun w => w * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * w)) + -1 * 2 * env "e" * env "g" * Φ "I1" w + -1 * env "b" * env "c" * Φ "I2" w := by
      funext w; simp [rubi734r134, eval, recEnv, Interp.real, i2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi734r134.body = (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      simp [rubi734r134, eval, Interp.real, i2]
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    refine ((((hasDerivAt_id t).mul hL).mul hM).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [id, Function.comp_def, Pi.mul_apply]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith [hd1, hd2])
    generalize Real.artanh (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    field_simp
    ring

theorem rubi731r154_real : rubi731r154.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r154.conditions rubi731r154.body rubi731r154.result rubi731r154.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r154.body →
      0 < env "f" + env "g" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r154, Defined, eval, Interp.real, i2] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hP, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r154, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.1
      have hDw' : (1 - (env "c" * w) ^ 2) ≠ 0 := (by nlinarith [hb.2.1, hb.2.2])
      simp [Defined, eval, Interp.real, i2, im1, hb.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r154, Defined, eval, recEnv, Interp.real, i2, hb.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi731r154, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ 2 * (env "a" + env "b" * Real.artanh (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1]
    have hΦ2' : HasDerivAt (Φ "I2") (t * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 - (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r154.integrals.map (·.1)) Φ "x" w) rubi731r154.result) =
        fun w => w * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * w)) + -1 * 2 * env "e" * env "g" * Φ "I1" w + -1 * env "b" * env "c" * Φ "I2" w := by
      funext w; simp [rubi731r154, eval, recEnv, Interp.real, i2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r154.body = (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * t)) := by
      simp [rubi731r154, eval, Interp.real, i2]
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    refine ((((hasDerivAt_id t).mul hL).mul hM).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [id, Function.comp_def, Pi.mul_apply]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith [hd1, hd2])
    generalize Real.artanh (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    field_simp
    ring

theorem rubi534r134_real : rubi534r134.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r134.conditions rubi534r134.body rubi534r134.result rubi534r134.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r134.body →
      0 < env "f" + env "g" * w ^ 2 ∧ True := by
    intro w h
    simp [rubi534r134, Defined, eval, Interp.real, i2] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨hP, -⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r134, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.1
      have hDw' : (1 + (env "c" * w) ^ 2) ≠ 0 := (by positivity)
      simp [Defined, eval, Interp.real, i2, im1, hb.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi534r134, Defined, eval, recEnv, Interp.real, i2, hb.1]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi534r134, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ 2 * (env "a" + env "b" * Real.arctan (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1]
    have hΦ2' : HasDerivAt (Φ "I2") (t * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 + (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r134.integrals.map (·.1)) Φ "x" w) rubi534r134.result) =
        fun w => w * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.arctan (env "c" * w)) + -1 * 2 * env "e" * env "g" * Φ "I1" w + -1 * env "b" * env "c" * Φ "I2" w := by
      funext w; simp [rubi534r134, eval, recEnv, Interp.real, i2]
    have hEF : eval Interp.real (Function.update env "x" t) rubi534r134.body = (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.arctan (env "c" * t)) := by
      simp [rubi534r134, eval, Interp.real, i2]
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((Real.hasDerivAt_arctan' _).comp t hcx).const_mul (env "b")).const_add (env "a")
    refine ((((hasDerivAt_id t).mul hL).mul hM).add (hΦ1'.const_mul _) |>.add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [id, Function.comp_def, Pi.mul_apply]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 + (env "c" * t) ^ 2) ≠ 0 := (by positivity)
    generalize Real.arctan (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    field_simp
    ring


end OSR.IntegrationRec132
