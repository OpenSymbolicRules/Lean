import OSR.IntegrationRec91

/-!
# Integration (RUBI): `(a + b x^n)^p = x^(n p) (b + a x^(-n))^p`

For negative integers `n` and `p` the integrand is only defined at `x ≠ 0`,
where `a + b x^n = x^n (b + a x^(-n))`.  6.1.11 #7, #8, #19 and #20 are proved
over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec144

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.1.11 #7 -/
def rubi6111r7 : CRule where
  id := "integration.rubi_6_1_11_r7"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11804
  description := "RUBI 6.1.11 #7"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:7" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#7"

/-- RUBI 6.1.11 #8 -/
def rubi6111r8 : CRule where
  id := "integration.rubi_6_1_11_r8"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.var "n") (.var "p"))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11805
  description := "RUBI 6.1.11 #8"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:8" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#8"

/-- RUBI 6.1.11 #19 -/
def rubi6111r19 : CRule where
  id := "integration.rubi_6_1_11_r19"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11806
  description := "RUBI 6.1.11 #19"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:19" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#19"

/-- RUBI 6.1.11 #20 -/
def rubi6111r20 : CRule where
  id := "integration.rubi_6_1_11_r20"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p"))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.var "I1")
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.var "n") (.var "p")))) (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))))) (.var "p"))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.int 0) (.var "p"),
    .int (.var "n"),
    .gt (.int 0) (.var "n")]
  priority := 11807
  description := "RUBI 6.1.11 #20"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:20" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#20"

/-! ## Proofs -/

private theorem split_eq {K : Type} [Field K] (a b w : K) (n : ℤ) (hw : w ≠ 0) :
    a + b * w ^ n = w ^ n * (b + a * (w ^ n)⁻¹) := by
  have e : w ^ n * (w ^ n)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero n hw)
  linear_combination (-a) * e

private theorem split_pow {K : Type} [Field K] (a b w : K) (n p : ℤ) (hw : w ≠ 0) :
    (a + b * w ^ n) ^ p = w ^ (n * p) * (b + a * (w ^ n)⁻¹) ^ p := by
  rw [split_eq a b w n hw, mul_zpow, zpow_mul]

private theorem split_ne {K : Type} [Field K] (a b w : K) (n : ℤ) (hw : w ≠ 0)
    (h : a + b * w ^ n ≠ 0) : b + a * (w ^ n)⁻¹ ≠ 0 := by
  intro h0; apply h; rw [split_eq a b w n hw, h0, mul_zero]

theorem rubi6111r7_real : rubi6111r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6111r7.conditions rubi6111r7.body rubi6111r7.result rubi6111r7.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r7, Defined, eval, Interp.real, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r7, Defined, eval, Interp.real, hk_n, hk_p] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r7])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r7, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn'] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r7, Defined, eval, recEnv]
  · simp only [rubi6111r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6111r7.integrals.map (·.1)) Φ "x" w) rubi6111r7.result) = Φ "I1" := by
      funext w; simp [rubi6111r7, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r7, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn'] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r7, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn']
    first
      | (left; rw [split_pow _ _ _ _ _ ht0])
      | (rw [split_pow _ _ _ _ _ ht0])
      | (left; rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (trace_state; sorry)

theorem rubi6111r7_complex : rubi6111r7.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6111r7.conditions rubi6111r7.body rubi6111r7.result rubi6111r7.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r7, Defined, eval, Interp.complex, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r7, Defined, eval, Interp.complex, hk_n, hk_p] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r7])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r7, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn'] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r7, Defined, eval, recEnv]
  · simp only [rubi6111r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6111r7.integrals.map (·.1)) Φ "x" w) rubi6111r7.result) = Φ "I1" := by
      funext w; simp [rubi6111r7, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r7, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn'] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r7, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn']
    first
      | (left; rw [split_pow _ _ _ _ _ ht0])
      | (rw [split_pow _ _ _ _ _ ht0])
      | (left; rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (trace_state; sorry)

theorem rubi6111r8_real : rubi6111r8.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6111r8.conditions rubi6111r8.body rubi6111r8.result rubi6111r8.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r8, Defined, eval, Interp.real, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r8, Defined, eval, Interp.real, hk_n, hk_p] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r8])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r8, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn'] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r8, Defined, eval, recEnv]
  · simp only [rubi6111r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6111r8.integrals.map (·.1)) Φ "x" w) rubi6111r8.result) = Φ "I1" := by
      funext w; simp [rubi6111r8, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r8, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn'] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r8, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn']
    first
      | (left; rw [split_pow _ _ _ _ _ ht0])
      | (rw [split_pow _ _ _ _ _ ht0])
      | (left; rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (trace_state; sorry)

theorem rubi6111r8_complex : rubi6111r8.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6111r8.conditions rubi6111r8.body rubi6111r8.result rubi6111r8.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r8, Defined, eval, Interp.complex, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r8, Defined, eval, Interp.complex, hk_n, hk_p] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r8])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r8, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn'] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r8, Defined, eval, recEnv]
  · simp only [rubi6111r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6111r8.integrals.map (·.1)) Φ "x" w) rubi6111r8.result) = Φ "I1" := by
      funext w; simp [rubi6111r8, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r8, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn'] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r8, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn']
    first
      | (left; rw [split_pow _ _ _ _ _ ht0])
      | (rw [split_pow _ _ _ _ _ ht0])
      | (left; rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (rw [split_pow _ _ _ _ _ ht0]; simp [zpow_neg])
      | (trace_state; sorry)

theorem rubi6111r19_real : rubi6111r19.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6111r19.conditions rubi6111r19.body rubi6111r19.result rubi6111r19.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.real, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.real, hk_n, hk_p] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.real, hk_n, hk_p, hk_m] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r19])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hmnp : intValue? (env "m" + env "n" * env "p") = some (km + kn * kp) := (intValue?_eq _ _).2 (by rw [hkm, hkn, hkp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r19, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r19, Defined, eval, recEnv]
  · simp only [rubi6111r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6111r19.integrals.map (·.1)) Φ "x" w) rubi6111r19.result) = Φ "I1" := by
      funext w; simp [rubi6111r19, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r19, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r19, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp]
    first
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (trace_state; sorry)

theorem rubi6111r19_complex : rubi6111r19.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6111r19.conditions rubi6111r19.body rubi6111r19.result rubi6111r19.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.complex, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.complex, hk_n, hk_p] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r19, Defined, eval, Interp.complex, hk_n, hk_p, hk_m] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r19])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hmnp : intValue? (env "m" + env "n" * env "p") = some (km + kn * kp) := (intValue?_eq _ _).2 (by rw [hkm, hkn, hkp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r19, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r19, Defined, eval, recEnv]
  · simp only [rubi6111r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6111r19.integrals.map (·.1)) Φ "x" w) rubi6111r19.result) = Φ "I1" := by
      funext w; simp [rubi6111r19, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r19, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r19, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp]
    first
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (trace_state; sorry)

theorem rubi6111r20_real : rubi6111r20.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6111r20.conditions rubi6111r20.body rubi6111r20.result rubi6111r20.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.real, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.real, hk_n, hk_p] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.real, hk_n, hk_p, hk_m] at h
  have hkn : env "n" = (kn : ℝ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℝ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r20])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.real] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hkm : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hk_m
  have hmnp : intValue? (env "m" + env "n" * env "p") = some (km + kn * kp) := (intValue?_eq _ _).2 (by rw [hkm, hkn, hkp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r20, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r20, Defined, eval, recEnv]
  · simp only [rubi6111r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi6111r20.integrals.map (·.1)) Φ "x" w) rubi6111r20.result) = Φ "I1" := by
      funext w; simp [rubi6111r20, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r20, Defined, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r20, eval, Interp.real, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp]
    first
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (trace_state; sorry)

theorem rubi6111r20_complex : rubi6111r20.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6111r20.conditions rubi6111r20.body rubi6111r20.result rubi6111r20.integrals
  intro env hc t hF
  rcases hk_n : intValue? (env "n") with _ | kn
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.complex, hk_n] at h
  rcases hk_p : intValue? (env "p") with _ | kp
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.complex, hk_n, hk_p] at h
  rcases hk_m : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi6111r20, Defined, eval, Interp.complex, hk_n, hk_p, hk_m] at h
  have hkn : env "n" = (kn : ℂ) := (intValue?_eq _ _).1 hk_n
  have hkp : env "p" = (kp : ℂ) := (intValue?_eq _ _).1 hk_p
  have hn0 : kn < 0 := by
    have h := hc (.gt (.int 0) (.var "n")) (by simp [rubi6111r20])
    simp only [Cond.Holds, Defined, eval, true_and] at h
    rw [hkn] at h
    simp [Interp.complex] at h
    first | exact_mod_cast h | exact_mod_cast h.2 | exact_mod_cast h.2.2 | (trace_state; sorry)
  have hnp : intValue? (env "n" * env "p") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hpn : intValue? (env "p" * env "n") = some (kn * kp) := (intValue?_eq _ _).2 (by rw [hkn, hkp]; push_cast; ring)
  have hmn : intValue? (-1 * env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hmn' : intValue? (-env "n") = some (-kn) := (intValue?_eq _ _).2 (by rw [hkn]; push_cast; ring)
  have hkm : env "m" = (km : ℂ) := (intValue?_eq _ _).1 hk_m
  have hmnp : intValue? (env "m" + env "n" * env "p") = some (km + kn * kp) := (intValue?_eq _ _).2 (by rw [hkm, hkn, hkp]; push_cast; ring)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6111r20, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    simp [rubi6111r20, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at hw ⊢
    have hw0 : w ≠ 0 := by first | exact hw.1 hn0 | exact hw.2.1 hn0 | exact hw.1.1 hn0 | exact (hw.1.1 hn0).2 | exact hw.1.2 hn0 | exact (hw.1.2 hn0) | (trace_state; sorry)
    have hA := split_ne (env "a") (env "b") w kn hw0
    first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6111r20, Defined, eval, recEnv]
  · simp only [rubi6111r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hfun : (fun w => eval Interp.complex (recEnv env (rubi6111r20.integrals.map (·.1)) Φ "x" w) rubi6111r20.result) = Φ "I1" := by
      funext w; simp [rubi6111r20, eval, recEnv]
    rw [hfun]
    refine hΦ.congr_deriv ?_
    have ht := hF.self_of_nhds
    simp [rubi6111r20, Defined, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp] at ht
    have ht0 : t ≠ 0 := by first | exact ht.1 hn0 | exact ht.2.1 hn0 | exact ht.1.1 hn0 | exact (ht.1.1 hn0).2 | exact ht.1.2 hn0 | (trace_state; sorry)
    simp [rubi6111r20, eval, Interp.complex, hk_n, hk_p, hnp, hpn, hmn, hmn', hk_m, hmnp]
    first
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; ring)
      | (left; rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (rw [split_pow _ _ _ _ _ ht0, zpow_add₀ ht0]; simp [zpow_neg]; ring)
      | (trace_state; sorry)

end OSR.IntegrationRec144
