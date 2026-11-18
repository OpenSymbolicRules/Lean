import OSR.IntegrationRec91

/-!
# Integration (RUBI): `xᵐ (d + e x²)^q (a + b A(c x))^p` split

`d (d + e x²)^q = (d + e x²)^(q+1) - e x² (d + e x²)^q`; the condition forces
`d ≠ 0` (otherwise `e = 0` and `(d + e x²)^q`, `q < -1`, is nowhere defined).
Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec141

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #95 -/
def rubi734r95 : CRule where
  id := "integration.rubi_7_3_4_r95"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:95"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .ne (.var "p") (.int (-1))]
  priority := 11701
  description := "RUBI 7.3.4 #95"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:95" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#95"

/-- RUBI 7.3.1 #115 -/
def rubi731r115 : CRule where
  id := "integration.rubi_7_3_1_r115"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:115"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .ne (.var "p") (.int (-1))]
  priority := 11702
  description := "RUBI 7.3.1 #115"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:115" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#115"

/-- RUBI 5.3.4 #95 -/
def rubi534r95 : CRule where
  id := "integration.rubi_5_3_4_r95"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:95"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .ne (.var "p") (.int (-1))]
  priority := 11703
  description := "RUBI 5.3.4 #95"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:95" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#95"

/-! ## Proofs -/

theorem rubi734r95_real : rubi734r95.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r95.conditions rubi734r95.body rubi734r95.result rubi734r95.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r95, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r95, Defined, eval, Interp.real, hk_m, hk_q, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r95, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  have hkm : km < 0 := by
    have h := hc (.gt (.int 0) (.var "m")) (by simp [rubi734r95])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkq : kq < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi734r95])
    simp [Cond.Holds, Defined, eval, Interp.real, h_q] at h; exact_mod_cast h
  have heq : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi734r95])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination h
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r95.body →
      w ≠ 0 ∧ env "d" + env "e" * w ^ 2 ≠ 0 ∧ (kp < 0 → env "a" + env "b" * Real.artanh (env "c" * w) ≠ 0) ∧ -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi734r95, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1, hkm, show kq < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨ht0, hB, -, -, -⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hB; rw [heq, h0]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r95, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1, show kq + 1 < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi734r95, Defined, eval, recEnv, Interp.real, i2, im1, hd0]
  · simp only [rubi734r95, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r95.integrals.map (·.1)) Φ "x" w) rubi734r95.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi734r95, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r95, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1]
    rw [zpow_add_one₀ hB kq, zpow_add₀ ht0 km 2]
    generalize t ^ km = X
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ kp = P
    generalize (env "d" + env "e" * t ^ 2) ^ kq = Q
    field_simp
    ring

theorem rubi731r115_real : rubi731r115.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r115.conditions rubi731r115.body rubi731r115.result rubi731r115.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r115, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r115, Defined, eval, Interp.real, hk_m, hk_q, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r115, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  have hkm : km < 0 := by
    have h := hc (.gt (.int 0) (.var "m")) (by simp [rubi731r115])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkq : kq < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi731r115])
    simp [Cond.Holds, Defined, eval, Interp.real, h_q] at h; exact_mod_cast h
  have heq : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi731r115])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination h
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r115.body →
      w ≠ 0 ∧ env "d" + env "e" * w ^ 2 ≠ 0 ∧ (kp < 0 → env "a" + env "b" * Real.artanh (env "c" * w) ≠ 0) ∧ -1 < env "c" * w ∧ env "c" * w < 1 := by
    intro w h
    simp [rubi731r115, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1, hkm, show kq < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨ht0, hB, -, -, -⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hB; rw [heq, h0]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r115, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1, show kq + 1 < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi731r115, Defined, eval, recEnv, Interp.real, i2, im1, hd0]
  · simp only [rubi731r115, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r115.integrals.map (·.1)) Φ "x" w) rubi731r115.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r115, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r115, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1]
    rw [zpow_add_one₀ hB kq, zpow_add₀ ht0 km 2]
    generalize t ^ km = X
    generalize (env "a" + env "b" * Real.artanh (env "c" * t)) ^ kp = P
    generalize (env "d" + env "e" * t ^ 2) ^ kq = Q
    field_simp
    ring

theorem rubi534r95_real : rubi534r95.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r95.conditions rubi534r95.body rubi534r95.result rubi534r95.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r95, Defined, eval, Interp.real, hk_m, i2, im1] at h
  rcases hk_q : intValue? (env "q") with _ | kq
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r95, Defined, eval, Interp.real, hk_m, hk_q, i2, im1] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r95, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1] at h
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have h_q : env "q" = (kq : ℝ) := (intValue?_eq _ _).1 hk_q
  have hkm : km < 0 := by
    have h := hc (.gt (.int 0) (.var "m")) (by simp [rubi534r95])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h; exact_mod_cast h
  have hkq : kq < -1 := by
    have h := hc (.gt (.int (-1)) (.var "q")) (by simp [rubi534r95])
    simp [Cond.Holds, Defined, eval, Interp.real, h_q] at h; exact_mod_cast h
  have heq : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r95])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h; linear_combination h
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have eq1 : intValue? (env "q" + 1) = some (kq + 1) := (intValue?_eq _ _).2 (by rw [h_q]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r95.body →
      w ≠ 0 ∧ env "d" + env "e" * w ^ 2 ≠ 0 ∧ (kp < 0 → env "a" + env "b" * Real.arctan (env "c" * w) ≠ 0) := by
    intro w h
    simp [rubi534r95, Defined, eval, Interp.real, hk_m, hk_q, hk_p, i2, im1, hkm, show kq < 0 by omega] at h
    first | tauto | (trace_state; sorry)
  obtain ⟨ht0, hB, -⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; apply hB; rw [heq, h0]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r95, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      simp [Defined, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1, show kq + 1 < 0 by omega] at hw ⊢
      first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi534r95, Defined, eval, recEnv, Interp.real, i2, im1, hd0]
  · simp only [rubi534r95, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r95.integrals.map (·.1)) Φ "x" w) rubi534r95.result) =
        fun w => 1 * (env "d")⁻¹ * Φ "I1" w + -1 * env "e" * (env "d")⁻¹ * Φ "I2" w := by
      funext w; simp [rubi534r95, eval, recEnv, Interp.real, i2, im1]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r95, eval, Interp.real, hk_m, hk_q, hk_p, em2, eq1, i2, im1]
    rw [zpow_add_one₀ hB kq, zpow_add₀ ht0 km 2]
    generalize t ^ km = X
    generalize (env "a" + env "b" * Real.arctan (env "c" * t)) ^ kp = P
    generalize (env "d" + env "e" * t ^ 2) ^ kq = Q
    field_simp
    ring


end OSR.IntegrationRec141
