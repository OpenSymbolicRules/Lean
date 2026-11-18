import OSR.IntegrationRec131

/-!
# Integration (RUBI): integration by parts of `xᵐ (d + e log(f + g x²)) (a + b A(c x))`

For `A = artanh` and `A = arctan`, with `m/2` a negative integer (so `m + 1 ≠ 0`
and `x ≠ 0` wherever the integrand is defined): the product rule on
`x^(m+1) L M/(m + 1)` leaves the two residual integrands.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec133

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #142 -/
def rubi734r142 : CRule where
  id := "integration.rubi_7_3_4_r142"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:142"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))),
    .gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 10901
  description := "RUBI 7.3.4 #142"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:142" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#142"

/-- RUBI 7.3.1 #162 -/
def rubi731r162 : CRule where
  id := "integration.rubi_7_3_1_r162"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:162"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))),
    .gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 10902
  description := "RUBI 7.3.1 #162"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:162" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#162"

/-- RUBI 5.3.4 #142 -/
def rubi534r142 : CRule where
  id := "integration.rubi_5_3_4_r142"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:142"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "e")) (.var "g")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m"]
  conditions := [.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))),
    .gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))]
  priority := 10903
  description := "RUBI 5.3.4 #142"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:142" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#142"

/-! ## Proofs -/

theorem rubi734r142_real : rubi734r142.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r142.conditions rubi734r142.body rubi734r142.result rubi734r142.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r142, Defined, eval, Interp.real, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  have hj := hc (.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi734r142])
  simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
  obtain ⟨j, hj⟩ := hj
  have hkj : k = 2 * j := by
    have := (intValue?_eq _ _).1 hj; rw [h_m] at this
    have : (k : ℝ) = 2 * j := by linarith
    exact_mod_cast this
  have hg := hc (.gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi734r142])
  simp [Cond.Holds, Defined, eval, Interp.real, im1, h_m] at hg
  have hk0 : k < 0 := by
    have : (k : ℝ) < 0 := by linarith
    exact_mod_cast this
  have hk1 : (k : ℝ) + 1 ≠ 0 := by
    have : (k + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (k + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r142.body →
      w ≠ 0 ∧ 0 < env "f" + env "g" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi734r142, Defined, eval, Interp.real, i2, hk_m, hk0] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨ht0, hP, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r142, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.2.1
      have hDw' : (1 - (env "c" * w) ^ 2) ≠ 0 := (by nlinarith [hb.2.2.1, hb.2.2.2])
      simp [Defined, eval, Interp.real, i2, im1, em1, em2, hb.1, hb.2.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi734r142, Defined, eval, recEnv, Interp.real, i2, im1, em1, hb.1, hb.2.1, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734r142, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ (k + 2) * (env "a" + env "b" * Real.artanh (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1, em2]
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 - (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1, em1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r142.integrals.map (·.1)) Φ "x" w) rubi734r142.result) =
        fun w => w ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * w)) * (env "m" + 1)⁻¹ + -1 * 2 * env "e" * env "g" * (env "m" + 1)⁻¹ * Φ "I1" w + -1 * env "b" * env "c" * (env "m" + 1)⁻¹ * Φ "I2" w := by
      funext w; simp [rubi734r142, eval, recEnv, Interp.real, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi734r142.body = t ^ k * ((env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * t))) := by
      simp [rubi734r142, eval, Interp.real, i2, hk_m]
      try ring1
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hX := hasDerivAt_zpow (k + 1) t (Or.inl ht0)
    refine (((((hX.mul hL).mul hM).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith [hd1, hd2])
    rw [zpow_add₀ ht0 k 2, zpow_add_one₀ ht0 k, h_m]
    generalize t ^ k = Tk
    generalize Real.artanh (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    push_cast
    field_simp
    ring

theorem rubi731r162_real : rubi731r162.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r162.conditions rubi731r162.body rubi731r162.result rubi731r162.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r162, Defined, eval, Interp.real, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  have hj := hc (.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi731r162])
  simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
  obtain ⟨j, hj⟩ := hj
  have hkj : k = 2 * j := by
    have := (intValue?_eq _ _).1 hj; rw [h_m] at this
    have : (k : ℝ) = 2 * j := by linarith
    exact_mod_cast this
  have hg := hc (.gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi731r162])
  simp [Cond.Holds, Defined, eval, Interp.real, im1, h_m] at hg
  have hk0 : k < 0 := by
    have : (k : ℝ) < 0 := by linarith
    exact_mod_cast this
  have hk1 : (k : ℝ) + 1 ≠ 0 := by
    have : (k + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (k + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r162.body →
      w ≠ 0 ∧ 0 < env "f" + env "g" * w ^ 2 ∧ (-1 < env "c" * w ∧ env "c" * w < 1) := by
    intro w h
    simp [rubi731r162, Defined, eval, Interp.real, i2, hk_m, hk0] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨ht0, hP, hd1, hd2⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r162, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.2.1
      have hDw' : (1 - (env "c" * w) ^ 2) ≠ 0 := (by nlinarith [hb.2.2.1, hb.2.2.2])
      simp [Defined, eval, Interp.real, i2, im1, em1, em2, hb.1, hb.2.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi731r162, Defined, eval, recEnv, Interp.real, i2, im1, em1, hb.1, hb.2.1, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi731r162, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ (k + 2) * (env "a" + env "b" * Real.artanh (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1, em2]
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 - (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1, em1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r162.integrals.map (·.1)) Φ "x" w) rubi731r162.result) =
        fun w => w ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * w)) * (env "m" + 1)⁻¹ + -1 * 2 * env "e" * env "g" * (env "m" + 1)⁻¹ * Φ "I1" w + -1 * env "b" * env "c" * (env "m" + 1)⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r162, eval, recEnv, Interp.real, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r162.body = t ^ k * ((env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.artanh (env "c" * t))) := by
      simp [rubi731r162, eval, Interp.real, i2, hk_m]
      try ring1
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hX := hasDerivAt_zpow (k + 1) t (Or.inl ht0)
    refine (((((hX.mul hL).mul hM).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith [hd1, hd2])
    rw [zpow_add₀ ht0 k 2, zpow_add_one₀ ht0 k, h_m]
    generalize t ^ k = Tk
    generalize Real.artanh (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    push_cast
    field_simp
    ring

theorem rubi534r142_real : rubi534r142.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r142.conditions rubi534r142.body rubi534r142.result rubi534r142.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r142, Defined, eval, Interp.real, hk_m] at h
  have h_m : env "m" = (k : ℝ) := (intValue?_eq _ _).1 hk_m
  have hj := hc (.int (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi534r142])
  simp [Cond.Holds, Defined, eval, Interp.real, im1] at hj
  obtain ⟨j, hj⟩ := hj
  have hkj : k = 2 * j := by
    have := (intValue?_eq _ _).1 hj; rw [h_m] at this
    have : (k : ℝ) = 2 * j := by linarith
    exact_mod_cast this
  have hg := hc (.gt (.int 0) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (by simp [rubi534r142])
  simp [Cond.Holds, Defined, eval, Interp.real, im1, h_m] at hg
  have hk0 : k < 0 := by
    have : (k : ℝ) < 0 := by linarith
    exact_mod_cast this
  have hk1 : (k : ℝ) + 1 ≠ 0 := by
    have : (k + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hk1
  have em1 : intValue? (env "m" + 1) = some (k + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (k + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r142.body →
      w ≠ 0 ∧ 0 < env "f" + env "g" * w ^ 2 ∧ True := by
    intro w h
    simp [rubi534r142, Defined, eval, Interp.real, i2, hk_m, hk0] at h
    first | exact h | tauto | (trace_state; sorry)
  obtain ⟨ht0, hP, -⟩ := hBody t hF.self_of_nhds
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r142, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hPw : env "f" + env "g" * w ^ 2 ≠ 0 := ne_of_gt hb.2.1
      have hDw' : (1 + (env "c" * w) ^ 2) ≠ 0 := (by positivity)
      simp [Defined, eval, Interp.real, i2, im1, em1, em2, hb.1, hb.2.1, hPw]
      first | done | tauto | (intro h0; apply hDw'; linear_combination h0) | (refine ⟨?_, ?_⟩ <;> first | tauto | (intro h0; apply hDw'; linear_combination h0)) | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    simp [rubi534r142, Defined, eval, recEnv, Interp.real, i2, im1, em1, hb.1, hb.2.1, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi534r142, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") (t ^ (k + 2) * (env "a" + env "b" * Real.arctan (env "c" * t)) * (env "f" + env "g" * t ^ 2)⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, i2, im1, em2]
    have hΦ2' : HasDerivAt (Φ "I2") (t ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (1 + (env "c" * t) ^ 2)⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, i2, im1, em1]; first | ring1 | (left; ring1) | (congr 1; ring1) | (trace_state; sorry)
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r142.integrals.map (·.1)) Φ "x" w) rubi534r142.result) =
        fun w => w ^ (k + 1) * (env "d" + env "e" * Real.log (env "f" + env "g" * w ^ 2)) * (env "a" + env "b" * Real.arctan (env "c" * w)) * (env "m" + 1)⁻¹ + -1 * 2 * env "e" * env "g" * (env "m" + 1)⁻¹ * Φ "I1" w + -1 * env "b" * env "c" * (env "m" + 1)⁻¹ * Φ "I2" w := by
      funext w; simp [rubi534r142, eval, recEnv, Interp.real, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi534r142.body = t ^ k * ((env "d" + env "e" * Real.log (env "f" + env "g" * t ^ 2)) * (env "a" + env "b" * Real.arctan (env "c" * t))) := by
      simp [rubi534r142, eval, Interp.real, i2, hk_m]
      try ring1
    rw [hfun, hEF]
    have hPd : HasDerivAt (fun w => env "f" + env "g" * w ^ 2) (env "g" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "g")).const_add (env "f")
    have hL := ((hPd.log (ne_of_gt hP)).const_mul (env "e")).const_add (env "d")
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((Real.hasDerivAt_arctan' _).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hX := hasDerivAt_zpow (k + 1) t (Or.inl ht0)
    refine (((((hX.mul hL).mul hM).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, add_sub_cancel_right]
    have hPt : env "f" + env "g" * t ^ 2 ≠ 0 := ne_of_gt hP
    have hDt' : (1 + (env "c" * t) ^ 2) ≠ 0 := (by positivity)
    rw [zpow_add₀ ht0 k 2, zpow_add_one₀ ht0 k, h_m]
    generalize t ^ k = Tk
    generalize Real.arctan (env "c" * t) = AT
    generalize Real.log (env "f" + env "g" * t ^ 2) = LG
    push_cast
    field_simp
    ring


end OSR.IntegrationRec133
