import OSR.IntegrationRec131

/-!
# Integration (RUBI): `∫ (a + b A(c x))^p/(x² √(d + e x²))` by parts

For `A = artanh` with `c² d + e = 0` and `A = arctan` with `e = c² d`, `p > 0`:
with `q = √(d + e x²)`, `q² = d (1 ∓ c² x²)`, so the derivative of
`-q M^p/(d x)` is the integrand minus `b c p M^(p-1)/(x q)`, the residual
integrand.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec136

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #89 -/
def rubi734r89 : CRule where
  id := "integration.rubi_7_3_4_r89"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:89"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.var "x")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 11201
  description := "RUBI 7.3.4 #89"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:89" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#89"

/-- RUBI 7.3.1 #109 -/
def rubi731r109 : CRule where
  id := "integration.rubi_7_3_1_r109"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:109"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.var "x")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 11202
  description := "RUBI 7.3.1 #109"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:109" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#109"

/-- RUBI 5.3.4 #89 -/
def rubi534r89 : CRule where
  id := "integration.rubi_5_3_4_r89"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:89"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.var "d") (.var "x")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0)]
  priority := 11203
  description := "RUBI 5.3.4 #89"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:89" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#89"

/-! ## Proofs -/

private theorem zpow_succ_of' (A : ℝ) (k : ℤ) (h : 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  lift k to ℕ using h
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, pow_succ]

theorem rubi734r89_real : rubi734r89.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r89.conditions rubi734r89.body rubi734r89.result rubi734r89.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi734r89])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r89, Defined, eval, Interp.real, hk, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi734r89])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r89.body →
      -1 < env "c" * w ∧ env "c" * w < 1 ∧ 0 < (env "d" + env "e" * w ^ 2) ∧ w ≠ 0 := by
    intro w h
    simp [rubi734r89, Defined, eval, Interp.real, hk, i2, im1, show ¬ k < 0 by omega] at h
    exact ⟨h.1.1, h.1.2, lt_of_le_of_ne h.2.1 (fun h0 => h.2.2.2 (by rw [← h0, Real.sqrt_zero])), h.2.2.1⟩
  obtain ⟨hd1, hd2, hQ, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r89, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hs := Real.sqrt_ne_zero'.2 (hb.2.2.1)
    have hle := (hb.2.2.1).le
    simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', show ¬ k - 1 < 0 by omega]
    first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.2.2.1).le
    simp [rubi734r89, Defined, eval, recEnv, Interp.real, hk, i2, im1, show ¬ k < 0 by omega, hd0]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734r89, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (t * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep']
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r89.integrals.map (·.1)) Φ "x" w) rubi734r89.result) =
        fun w => -1 * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (env "d" * w)⁻¹ + env "b" * env "c" * env "p" * Φ "I1" w := by
      funext w; simp [rubi734r89, eval, recEnv, Interp.real, hk, i2, im1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi734r89.body = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (t ^ 2 * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi734r89, eval, Interp.real, hk, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hdx := ((hasDerivAt_id t).const_mul (env "d")).inv (mul_ne_zero hd0 ht0)
    refine ((((hq.const_mul (-1)).mul hMk).mul hdx).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one]
    have hD1 : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith)
    have hD1' : (1 - env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 - env "c" ^ 2 * t ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring, h_p]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.artanh (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (-(env "c" ^ 2 * env "d")) * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 - (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    field_simp
    ring

theorem rubi731r109_real : rubi731r109.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r109.conditions rubi731r109.body rubi731r109.result rubi731r109.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi731r109])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r109, Defined, eval, Interp.real, hk, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r109])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r109.body →
      -1 < env "c" * w ∧ env "c" * w < 1 ∧ 0 < (env "d" + env "e" * w ^ 2) ∧ w ≠ 0 := by
    intro w h
    simp [rubi731r109, Defined, eval, Interp.real, hk, i2, im1, show ¬ k < 0 by omega] at h
    exact ⟨h.1.1, h.1.2, lt_of_le_of_ne h.2.1 (fun h0 => h.2.2.2 (by rw [← h0, Real.sqrt_zero])), h.2.2.1⟩
  obtain ⟨hd1, hd2, hQ, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r109, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hs := Real.sqrt_ne_zero'.2 (hb.2.2.1)
    have hle := (hb.2.2.1).le
    simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', show ¬ k - 1 < 0 by omega]
    first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.2.2.1).le
    simp [rubi731r109, Defined, eval, recEnv, Interp.real, hk, i2, im1, show ¬ k < 0 by omega, hd0]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi731r109, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (t * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep']
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r109.integrals.map (·.1)) Φ "x" w) rubi731r109.result) =
        fun w => -1 * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (env "d" * w)⁻¹ + env "b" * env "c" * env "p" * Φ "I1" w := by
      funext w; simp [rubi731r109, eval, recEnv, Interp.real, hk, i2, im1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r109.body = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (t ^ 2 * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi731r109, eval, Interp.real, hk, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hdx := ((hasDerivAt_id t).const_mul (env "d")).inv (mul_ne_zero hd0 ht0)
    refine ((((hq.const_mul (-1)).mul hMk).mul hdx).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one]
    have hD1 : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith)
    have hD1' : (1 - env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 - env "c" ^ 2 * t ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring, h_p]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.artanh (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (-(env "c" ^ 2 * env "d")) * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 - (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    field_simp
    ring

theorem rubi534r89_real : rubi534r89.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r89.conditions rubi534r89.body rubi534r89.result rubi534r89.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r89])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r89, Defined, eval, Interp.real, hk, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi534r89])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r89.body →
      0 < (env "d" + env "e" * w ^ 2) ∧ w ≠ 0 := by
    intro w h
    simp [rubi534r89, Defined, eval, Interp.real, hk, i2, im1, show ¬ k < 0 by omega] at h
    exact ⟨lt_of_le_of_ne h.1 (fun h0 => h.2.2 (by rw [← h0, Real.sqrt_zero])), h.2.1⟩
  obtain ⟨hQ, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r89, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hs := Real.sqrt_ne_zero'.2 (hb.1)
    have hle := (hb.1).le
    simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', show ¬ k - 1 < 0 by omega]
    first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.1).le
    simp [rubi534r89, Defined, eval, recEnv, Interp.real, hk, i2, im1, show ¬ k < 0 by omega, hd0]
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi534r89, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hΦ
    have hΦ' : HasDerivAt (Φ "I1") ((env "a" + env "b" * Real.arctan (env "c" * t)) ^ (k - 1) * (t * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep']
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r89.integrals.map (·.1)) Φ "x" w) rubi534r89.result) =
        fun w => -1 * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.arctan (env "c" * w)) ^ k * (env "d" * w)⁻¹ + env "b" * env "c" * env "p" * Φ "I1" w := by
      funext w; simp [rubi534r89, eval, recEnv, Interp.real, hk, i2, im1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi534r89.body = (env "a" + env "b" * Real.arctan (env "c" * t)) ^ k * (t ^ 2 * Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi534r89, eval, Interp.real, hk, i2, im1]
    rw [hfun, hEF]
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hM := (((Real.hasDerivAt_arctan' _).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hdx := ((hasDerivAt_id t).const_mul (env "d")).inv (mul_ne_zero hd0 ht0)
    refine ((((hq.const_mul (-1)).mul hMk).mul hdx).add (hΦ'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one]
    have hD1 : (1 + (env "c" * t) ^ 2) ≠ 0 := (by positivity)
    have hD1' : (1 + env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 + env "c" ^ 2 * t ^ 2) = (1 + (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.arctan (env "c" * t)) ^ k = (env "a" + env "b" * Real.arctan (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.arctan (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring, h_p]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.arctan (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (env "c" ^ 2 * env "d") * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 + (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    field_simp
    ring


end OSR.IntegrationRec136
