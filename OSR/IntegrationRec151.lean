import OSR.IntegrationRec91

/-!
# Integration (RUBI): half-argument forms of `g (1 ± cosh u)`

`1 + cosh u = 2 cosh²(u/2)`, `cosh u - 1 = 2 sinh²(u/2)` and
`sinh u = 2 sinh(u/2) cosh(u/2)`.  6.7.7 #24 and #25 are proved over ℝ and ℂ,
6.7.7 #30 over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec151

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.7.7 #24 -/
def rubi677r24 : CRule where
  id := "integration.rubi_6_7_7_r24"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "n")) (.pow (.var "g") (.var "n"))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11838
  description := "RUBI 6.7.7 #24"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:24" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#24"

/-- RUBI 6.7.7 #25 -/
def rubi677r25 : CRule where
  id := "integration.rubi_6_7_7_r25"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "n")) (.pow (.var "g") (.var "n"))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.var "g")) (.int 0),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11839
  description := "RUBI 6.7.7 #25"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:25" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#25"

/-- RUBI 6.7.7 #30 -/
def rubi677r30 : CRule where
  id := "integration.rubi_6_7_7_r30"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.pow (.var "g") (.var "n")) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.var "m"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0),
    .int (.var "m"),
    .int (.var "n"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0)]
  priority := 11840
  description := "RUBI 6.7.7 #30"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:30" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#30"

/-! ## Proofs -/

theorem rubi677r24_real : rubi677r24.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r24.conditions rubi677r24.body rubi677r24.result rubi677r24.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r24, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n2 : intValue? (2 * env "n") = some (2 * kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hfg : env "f" = env "g" := by
    have h := hc (.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0)) (by simp [rubi677r24])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi677r24])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hv : ∀ w : ℝ, env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := fun w => by ring
  have hc1 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 - 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hc2 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 + 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hs1 : ∀ w : ℝ, Real.sinh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := by
    intro w; rw [hv, Real.sinh_two_mul]
  have hfac : ∀ w : ℝ, env "f" + env "g" * Real.cosh (env "d" + env "e" * w) = 2 * env "g" * (Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)) := by
    intro w; rw [hfg, hc1]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r24, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    rcases hq : intValue? (env "c" * (env "a" + env "b" * w)) with _ | q <;>
    simp [rubi677r24, Defined, eval, Interp.real, i2, im1, hk_n, n2, hq] at hw ⊢
    rw [hfac] at hw
    refine ⟨hw.1, ?_⟩
    intro hk h0
    first
      | (exact (hw.2 (by omega)) (by rw [h0]; simp))
      | (exact (hw.2 (by omega)) (by rw [show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from h0]; simp))
      | (apply hw.2 (by omega); rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [hs1]
         rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [show (env "d" + env "e" * w) = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from (by
           rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Real.sinh_eq_zero] at h0
           rcases h0 with h0 | h0
           · exact h0
           · exact absurd h0 (Real.cosh_pos _).ne')]; ring)
      | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi677r24, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2] at hw ⊢
    intro hk hg
    rw [hfac, hg] at hw
    first | exact hw.2 (by omega) (by ring) | (simp at hw; omega) | (trace_state; sorry)
  · simp only [rubi677r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" * (env "a" + env "b" * t)) with _ | q <;>
    simp [rubi677r24, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2, hq] at ht hΦ ⊢
    refine (hΦ.const_mul _).congr_deriv ?_
    rw [hfac]
    have hne := ht.2 hn0
    rw [hfac] at hne
    have hc0 : Real.cosh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) ≠ 0 := fun h => hne (by rw [h]; ring)
    rw [mul_zpow, mul_zpow, mul_zpow, show (2 : ℤ) * kn = kn + kn by ring, zpow_add₀ hc0]
    ring

theorem rubi677r24_complex : rubi677r24.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi677r24.conditions rubi677r24.body rubi677r24.result rubi677r24.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r24, Defined, eval, Interp.complex, hk_n] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have n2 : intValue? (2 * env "n") = some (2 * kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hfg : env "f" = env "g" := by
    have h := hc (.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0)) (by simp [rubi677r24])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi677r24])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hv : ∀ w : ℂ, env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := fun w => by ring
  have hc1 : ∀ w : ℂ, Complex.cosh (env "d" + env "e" * w) = 2 * Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 - 1 := by
    intro w; rw [hv, Complex.cosh_two_mul]; linear_combination -Complex.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hc2 : ∀ w : ℂ, Complex.cosh (env "d" + env "e" * w) = 2 * Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 + 1 := by
    intro w; rw [hv, Complex.cosh_two_mul]; linear_combination Complex.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hs1 : ∀ w : ℂ, Complex.sinh (env "d" + env "e" * w) = 2 * Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := by
    intro w; rw [hv, Complex.sinh_two_mul]
  have hfac : ∀ w : ℂ, env "f" + env "g" * Complex.cosh (env "d" + env "e" * w) = 2 * env "g" * (Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)) := by
    intro w; rw [hfg, hc1]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r24, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    rcases hq : intValue? (env "c" * (env "a" + env "b" * w)) with _ | q <;>
    simp [rubi677r24, Defined, eval, Interp.complex, i2, im1, hk_n, n2, hq] at hw ⊢
    rw [hfac] at hw
    refine ⟨hw.1, ?_⟩
    intro hk h0
    first
      | (exact (hw.2 (by omega)) (by rw [h0]; simp))
      | (exact (hw.2 (by omega)) (by rw [show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from h0]; simp))
      | (apply hw.2 (by omega); rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [hs1]
         rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [show (env "d" + env "e" * w) = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from (by
           rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Complex.sinh_eq_zero] at h0
           rcases h0 with h0 | h0
           · exact h0
           · exact absurd h0 (Complex.cosh_pos _).ne')]; ring)
      | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi677r24, Defined, eval, recEnv, Interp.complex, i2, im1, hk_n, n2] at hw ⊢
    intro hk hg
    rw [hfac, hg] at hw
    first | exact hw.2 (by omega) (by ring) | (simp at hw; omega) | (trace_state; sorry)
  · simp only [rubi677r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" * (env "a" + env "b" * t)) with _ | q <;>
    simp [rubi677r24, Defined, eval, recEnv, Interp.complex, i2, im1, hk_n, n2, hq] at ht hΦ ⊢
    refine (hΦ.const_mul _).congr_deriv ?_
    rw [hfac]
    have hne := ht.2 hn0
    rw [hfac] at hne
    have hc0 : Complex.cosh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) ≠ 0 := fun h => hne (by rw [h]; ring)
    rw [mul_zpow, mul_zpow, mul_zpow, show (2 : ℤ) * kn = kn + kn by ring, zpow_add₀ hc0]
    ring

theorem rubi677r25_real : rubi677r25.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r25.conditions rubi677r25.body rubi677r25.result rubi677r25.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r25, Defined, eval, Interp.real, hk_n] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n2 : intValue? (2 * env "n") = some (2 * kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hfg : env "f" = -env "g" := by
    have h := hc (.eq (.app2 .add (.var "f") (.var "g")) (.int 0)) (by simp [rubi677r25])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi677r25])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hv : ∀ w : ℝ, env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := fun w => by ring
  have hc1 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 - 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hc2 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 + 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hs1 : ∀ w : ℝ, Real.sinh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := by
    intro w; rw [hv, Real.sinh_two_mul]
  have hfac : ∀ w : ℝ, env "f" + env "g" * Real.cosh (env "d" + env "e" * w) = 2 * env "g" * (Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)) := by
    intro w; rw [hfg, hc2]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r25, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    rcases hq : intValue? (env "c" * (env "a" + env "b" * w)) with _ | q <;>
    simp [rubi677r25, Defined, eval, Interp.real, i2, im1, hk_n, n2, hq] at hw ⊢
    rw [hfac] at hw
    refine ⟨hw.1, ?_⟩
    intro hk h0
    first
      | (exact (hw.2 (by omega)) (by rw [h0]; simp))
      | (exact (hw.2 (by omega)) (by rw [show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from h0]; simp))
      | (apply hw.2 (by omega); rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [hs1]
         rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [show (env "d" + env "e" * w) = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from (by
           rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Real.sinh_eq_zero] at h0
           rcases h0 with h0 | h0
           · exact h0
           · exact absurd h0 (Real.cosh_pos _).ne')]; ring)
      | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi677r25, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2] at hw ⊢
    intro hk hg
    rw [hfac, hg] at hw
    first | exact hw.2 (by omega) (by ring) | (simp at hw; omega) | (trace_state; sorry)
  · simp only [rubi677r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" * (env "a" + env "b" * t)) with _ | q <;>
    simp [rubi677r25, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2, hq] at ht hΦ ⊢
    refine (hΦ.const_mul _).congr_deriv ?_
    rw [hfac]
    have hne := ht.2 hn0
    rw [hfac] at hne
    have hc0 : Real.sinh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) ≠ 0 := fun h => hne (by rw [h]; ring)
    rw [mul_zpow, mul_zpow, mul_zpow, show (2 : ℤ) * kn = kn + kn by ring, zpow_add₀ hc0]
    ring

theorem rubi677r25_complex : rubi677r25.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi677r25.conditions rubi677r25.body rubi677r25.result rubi677r25.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℂ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r25, Defined, eval, Interp.complex, hk_n] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have n2 : intValue? (2 * env "n") = some (2 * kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hfg : env "f" = -env "g" := by
    have h := hc (.eq (.app2 .add (.var "f") (.var "g")) (.int 0)) (by simp [rubi677r25])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi677r25])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2.2 | exact_mod_cast h.2
  have hv : ∀ w : ℂ, env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := fun w => by ring
  have hc1 : ∀ w : ℂ, Complex.cosh (env "d" + env "e" * w) = 2 * Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 - 1 := by
    intro w; rw [hv, Complex.cosh_two_mul]; linear_combination -Complex.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hc2 : ∀ w : ℂ, Complex.cosh (env "d" + env "e" * w) = 2 * Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 + 1 := by
    intro w; rw [hv, Complex.cosh_two_mul]; linear_combination Complex.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hs1 : ∀ w : ℂ, Complex.sinh (env "d" + env "e" * w) = 2 * Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Complex.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := by
    intro w; rw [hv, Complex.sinh_two_mul]
  have hfac : ∀ w : ℂ, env "f" + env "g" * Complex.cosh (env "d" + env "e" * w) = 2 * env "g" * (Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Complex.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)) := by
    intro w; rw [hfg, hc2]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r25, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    rcases hq : intValue? (env "c" * (env "a" + env "b" * w)) with _ | q <;>
    simp [rubi677r25, Defined, eval, Interp.complex, i2, im1, hk_n, n2, hq] at hw ⊢
    rw [hfac] at hw
    refine ⟨hw.1, ?_⟩
    intro hk h0
    first
      | (exact (hw.2 (by omega)) (by rw [h0]; simp))
      | (exact (hw.2 (by omega)) (by rw [show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from h0]; simp))
      | (apply hw.2 (by omega); rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [hs1]
         rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [show (env "d" + env "e" * w) = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from (by
           rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Complex.sinh_eq_zero] at h0
           rcases h0 with h0 | h0
           · exact h0
           · exact absurd h0 (Complex.cosh_pos _).ne')]; ring)
      | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi677r25, Defined, eval, recEnv, Interp.complex, i2, im1, hk_n, n2] at hw ⊢
    intro hk hg
    rw [hfac, hg] at hw
    first | exact hw.2 (by omega) (by ring) | (simp at hw; omega) | (trace_state; sorry)
  · simp only [rubi677r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" * (env "a" + env "b" * t)) with _ | q <;>
    simp [rubi677r25, Defined, eval, recEnv, Interp.complex, i2, im1, hk_n, n2, hq] at ht hΦ ⊢
    refine (hΦ.const_mul _).congr_deriv ?_
    rw [hfac]
    have hne := ht.2 hn0
    rw [hfac] at hne
    have hc0 : Complex.sinh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) ≠ 0 := fun h => hne (by rw [h]; ring)
    rw [mul_zpow, mul_zpow, mul_zpow, show (2 : ℤ) * kn = kn + kn by ring, zpow_add₀ hc0]
    ring

theorem rubi677r30_real : rubi677r30.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi677r30.conditions rubi677r30.body rubi677r30.result rubi677r30.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r30, Defined, eval, Interp.real, hk_n] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi677r30, Defined, eval, Interp.real, hk_m] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have n2 : intValue? (2 * env "n") = some (2 * kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hfg : env "f" = env "g" := by
    have h := hc (.eq (.app2 .add (.var "f") (.app2 .mul (.int (-1)) (.var "g"))) (.int 0)) (by simp [rubi677r30])
    simp [Cond.Holds, Defined, eval] at h; linear_combination h
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hmn : km = -kn := by
    have h := hc (.eq (.app2 .add (.var "m") (.var "n")) (.int 0)) (by simp [rubi677r30])
    simp [Cond.Holds, Defined, eval, hkm, hkn] at h
    have : ((km + kn : ℤ) : ℝ) = 0 := by push_cast; linear_combination h
    have : km + kn = 0 := by exact_mod_cast this
    omega
  have hv : ∀ w : ℝ, env "d" + env "e" * w = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := fun w => by ring
  have hc1 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 - 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination -Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hc2 : ∀ w : ℝ, Real.cosh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) ^ 2 + 1 := by
    intro w; rw [hv, Real.cosh_two_mul]; linear_combination Real.cosh_sq_sub_sinh_sq (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)
  have hs1 : ∀ w : ℝ, Real.sinh (env "d" + env "e" * w) = 2 * Real.sinh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) := by
    intro w; rw [hv, Real.sinh_two_mul]
  have hfac : ∀ w : ℝ, env "f" + env "g" * Real.cosh (env "d" + env "e" * w) = 2 * env "g" * (Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) * Real.cosh (env "d" * 2⁻¹ + env "e" * w * 2⁻¹)) := by
    intro w; rw [hfg, hc1]; ring
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r30, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    rcases hq : intValue? (env "c" * (env "a" + env "b" * w)) with _ | q <;>
    simp [rubi677r30, Defined, eval, Interp.real, i2, im1, hk_n, n2, hk_m, hq] at hw ⊢
    rw [hfac] at hw
    refine ⟨hw.1.1, ?_⟩
    intro hk h0
    first
      | (exact (hw.2 (by omega)) (by rw [h0]; simp))
      | (exact (hw.2 (by omega)) (by rw [show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from h0]; simp))
      | (apply hw.2 (by omega); rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [hs1]
         rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at h0
         rcases h0 with h0 | h0
         · rw [h0]; ring
         · rw [h0]; ring)
      | (apply hw.1.2 (by omega); rw [show (env "d" + env "e" * w) = 2 * (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) by ring, show (env "d" * 2⁻¹ + env "e" * w * 2⁻¹) = 0 from (by
           rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff, Real.sinh_eq_zero] at h0
           rcases h0 with h0 | h0
           · exact h0
           · exact absurd h0 (Real.cosh_pos _).ne')]; ring)
      | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    simp [rubi677r30, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2, hk_m] at hw ⊢
    intro hk hg
    rw [hfac, hg] at hw
    first | exact hw.2 (by omega) (by ring) | (simp at hw; omega) | (trace_state; sorry)
  · simp only [rubi677r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have ht := hF.self_of_nhds
    rcases hq : intValue? (env "c" * (env "a" + env "b" * t)) with _ | q <;>
    simp [rubi677r30, Defined, eval, recEnv, Interp.real, i2, im1, hk_n, n2, hk_m, hq] at ht hΦ ⊢
    refine (hΦ.const_mul _).congr_deriv ?_
    rw [hfac, hs1]
    subst hmn
    rw [Real.tanh_eq_sinh_div_cosh]
    have hc0 : Real.cosh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) ≠ 0 := (Real.cosh_pos _).ne'
    generalize Real.sinh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) = s at *
    generalize Real.cosh (env "d" * 2⁻¹ + env "e" * t * 2⁻¹) = c at *
    rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rcases eq_or_ne kn 0 with h | h
      · subst h; simp
      · simp [zero_zpow _ (neg_ne_zero.2 h)]
    · simp only [mul_zpow, div_zpow, zpow_neg]
      field_simp

end OSR.IntegrationRec151
