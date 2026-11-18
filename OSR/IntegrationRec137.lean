import OSR.IntegrationRec131

/-!
# Integration (RUBI): `∫ (f x)^m (a + b A(c x))^p/√(d + e x²)` by parts

For `A = artanh` with `c² d + e = 0` and `A = arctan` with `e = c² d`, `p > 0`:
`m < -1`, `m ≠ -2`: with `q = √(d + e x²)`, `q² = d (1 ∓ c² x²)`, the derivative
of `(f x)^(m+1) q M^p/(d f (m + 1))` is the integrand plus the two residual
integrands with the opposite coefficients.  Proved over ℝ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec137

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #91 -/
def rubi734r91 : CRule where
  id := "integration.rubi_7_3_4_r91"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:91"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.var "m") (.int (-2))]
  priority := 11301
  description := "RUBI 7.3.4 #91"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:91" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#91"

/-- RUBI 7.3.1 #111 -/
def rubi731r111 : CRule where
  id := "integration.rubi_7_3_1_r111"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:111"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.var "m") (.int (-2))]
  priority := 11302
  description := "RUBI 7.3.1 #111"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:111" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#111"

/-- RUBI 5.3.4 #91 -/
def rubi534r91 : CRule where
  id := "integration.rubi_5_3_4_r91"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:91"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.var "m") (.int (-2))]
  priority := 11303
  description := "RUBI 5.3.4 #91"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:91" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#91"

/-! ## Proofs -/

private theorem zpow_succ_of' (A : ℝ) (k : ℤ) (h : 0 ≤ k) : A ^ (k + 1) = A ^ k * A := by
  lift k to ℕ using h
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, pow_succ]

theorem rubi734r91_real : rubi734r91.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r91.conditions rubi734r91.body rubi734r91.result rubi734r91.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi734r91])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r91, Defined, eval, Interp.real, hk, i2, im1] at h
  rcases hkm : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi734r91, Defined, eval, Interp.real, hk, hkm, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hkm
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi734r91])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have hkm0 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi734r91])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h
    exact_mod_cast h
  have hm1 : (km : ℝ) + 1 ≠ 0 := by
    have : (km + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hm1
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi734r91.body →
      -1 < env "c" * w ∧ env "c" * w < 1 ∧ 0 < (env "d" + env "e" * w ^ 2) ∧ env "f" ≠ 0 ∧ w ≠ 0 := by
    intro w h
    simp [rubi734r91, Defined, eval, Interp.real, hk, hkm, i2, im1, show ¬ k < 0 by omega, show km < 0 by omega] at h
    have hsq : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    have hle : 0 ≤ (env "d" + env "e" * w ^ 2) := by tauto
    have hlt : 0 < (env "d" + env "e" * w ^ 2) := lt_of_le_of_ne hle (fun h0 => hsq (by rw [← h0, Real.sqrt_zero]))
    first | tauto | (trace_state; sorry)
  obtain ⟨hd1, hd2, hQ, hf0, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r91, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hs := Real.sqrt_ne_zero'.2 (hb.2.2.1)
      have hle := (hb.2.2.1).le
      simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', em1, em2, show ¬ k - 1 < 0 by omega, show ¬ k < 0 by omega]
      first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.2.2.1).le
    simp [rubi734r91, Defined, eval, recEnv, Interp.real, hk, i2, im1, em1, show ¬ k < 0 by omega, hd0, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi734r91, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (km + 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep', em1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (km + 2) * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, hk, i2, im1, em2]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi734r91.integrals.map (·.1)) Φ "x" w) rubi734r91.result) =
        fun w => (env "f" * w) ^ (km + 1) * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (env "d" * env "f" * (env "m" + 1))⁻¹
          + -1 * env "b" * env "c" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w
          + 1 * env "c" ^ 2 * (env "m" + 2) * (env "f" ^ 2 * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w; simp [rubi734r91, eval, recEnv, Interp.real, hk, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi734r91.body = (env "f" * t) ^ km * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi734r91, eval, Interp.real, hk, hkm, i2, im1]
    rw [hfun, hEF]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hfx : HasDerivAt (fun w => env "f" * w) (env "f") t := by
      simpa using (hasDerivAt_id t).const_mul (env "f")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hX := (hasDerivAt_zpow (km + 1) _ (Or.inl hft)).comp t hfx
    refine (((((hX.mul hq).mul hMk).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one, add_sub_cancel_right]
    have hD1 : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith)
    have hD1' : (1 - env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 - env "c" ^ 2 * t ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    have hD1'' : (1 - t ^ 2 * env "c" ^ 2) ≠ 0 := by rw [show (1 - t ^ 2 * env "c" ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring,
      zpow_add₀ hft km 2, zpow_add_one₀ hft km, h_p, h_m]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.artanh (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    generalize (env "f" * t) ^ km = X
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (-(env "c" ^ 2 * env "d")) * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 - (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    push_cast
    have hm1x : 1 + (km : ℝ) ≠ 0 := by rw [add_comm]; exact hm1
    field_simp
    first | ring1 | (push_cast; ring1) | (simp only [Int.cast_add, Int.cast_one]; ring1) | (trace_state; sorry)

theorem rubi731r111_real : rubi731r111.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r111.conditions rubi731r111.body rubi731r111.result rubi731r111.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = -(env "c" ^ 2 * env "d") := by
    have h := hc (.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)) (by simp [rubi731r111])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r111, Defined, eval, Interp.real, hk, i2, im1] at h
  rcases hkm : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi731r111, Defined, eval, Interp.real, hk, hkm, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hkm
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi731r111])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have hkm0 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi731r111])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h
    exact_mod_cast h
  have hm1 : (km : ℝ) + 1 ≠ 0 := by
    have : (km + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hm1
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi731r111.body →
      -1 < env "c" * w ∧ env "c" * w < 1 ∧ 0 < (env "d" + env "e" * w ^ 2) ∧ env "f" ≠ 0 ∧ w ≠ 0 := by
    intro w h
    simp [rubi731r111, Defined, eval, Interp.real, hk, hkm, i2, im1, show ¬ k < 0 by omega, show km < 0 by omega] at h
    have hsq : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    have hle : 0 ≤ (env "d" + env "e" * w ^ 2) := by tauto
    have hlt : 0 < (env "d" + env "e" * w ^ 2) := lt_of_le_of_ne hle (fun h0 => hsq (by rw [← h0, Real.sqrt_zero]))
    first | tauto | (trace_state; sorry)
  obtain ⟨hd1, hd2, hQ, hf0, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r111, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hs := Real.sqrt_ne_zero'.2 (hb.2.2.1)
      have hle := (hb.2.2.1).le
      simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', em1, em2, show ¬ k - 1 < 0 by omega, show ¬ k < 0 by omega]
      first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.2.2.1).le
    simp [rubi731r111, Defined, eval, recEnv, Interp.real, hk, i2, im1, em1, show ¬ k < 0 by omega, hd0, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi731r111, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (km + 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep', em1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (km + 2) * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, hk, i2, im1, em2]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi731r111.integrals.map (·.1)) Φ "x" w) rubi731r111.result) =
        fun w => (env "f" * w) ^ (km + 1) * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.artanh (env "c" * w)) ^ k * (env "d" * env "f" * (env "m" + 1))⁻¹
          + -1 * env "b" * env "c" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w
          + 1 * env "c" ^ 2 * (env "m" + 2) * (env "f" ^ 2 * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w; simp [rubi731r111, eval, recEnv, Interp.real, hk, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi731r111.body = (env "f" * t) ^ km * (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi731r111, eval, Interp.real, hk, hkm, i2, im1]
    rw [hfun, hEF]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hfx : HasDerivAt (fun w => env "f" * w) (env "f") t := by
      simpa using (hasDerivAt_id t).const_mul (env "f")
    have hM := (((OSR.IntegrationRec131.hasDerivAt_artanh hd1 hd2).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hX := (hasDerivAt_zpow (km + 1) _ (Or.inl hft)).comp t hfx
    refine (((((hX.mul hq).mul hMk).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one, add_sub_cancel_right]
    have hD1 : (1 - (env "c" * t) ^ 2) ≠ 0 := (by nlinarith)
    have hD1' : (1 - env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 - env "c" ^ 2 * t ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    have hD1'' : (1 - t ^ 2 * env "c" ^ 2) ≠ 0 := by rw [show (1 - t ^ 2 * env "c" ^ 2) = (1 - (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.artanh (env "c" * t)) ^ k = (env "a" + env "b" * Real.artanh (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.artanh (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring,
      zpow_add₀ hft km 2, zpow_add_one₀ hft km, h_p, h_m]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.artanh (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    generalize (env "f" * t) ^ km = X
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (-(env "c" ^ 2 * env "d")) * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 - (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    push_cast
    have hm1x : 1 + (km : ℝ) ≠ 0 := by rw [add_comm]; exact hm1
    field_simp
    first | ring1 | (push_cast; ring1) | (simp only [Int.cast_add, Int.cast_one]; ring1) | (trace_state; sorry)

theorem rubi534r91_real : rubi534r91.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi534r91.conditions rubi534r91.body rubi534r91.result rubi534r91.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have he : env "e" = env "c" ^ 2 * env "d" := by
    have h := hc (.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))) (by simp [rubi534r91])
    simp [Cond.Holds, Defined, eval, Interp.real, i2] at h
    linear_combination h
  rcases hk : intValue? (env "p") with _ | k
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r91, Defined, eval, Interp.real, hk, i2, im1] at h
  rcases hkm : intValue? (env "m") with _ | km
  · exfalso; have h := hF.self_of_nhds; simp [rubi534r91, Defined, eval, Interp.real, hk, hkm, i2, im1] at h
  have h_p : env "p" = (k : ℝ) := (intValue?_eq _ _).1 hk
  have h_m : env "m" = (km : ℝ) := (intValue?_eq _ _).1 hkm
  have hk0 : 0 < k := by
    have h := hc (.gt (.var "p") (.int 0)) (by simp [rubi534r91])
    simp [Cond.Holds, Defined, eval, Interp.real, h_p] at h
    exact_mod_cast h
  have hkm0 : km < -1 := by
    have h := hc (.gt (.int (-1)) (.var "m")) (by simp [rubi534r91])
    simp [Cond.Holds, Defined, eval, Interp.real, h_m] at h
    exact_mod_cast h
  have hm1 : (km : ℝ) + 1 ≠ 0 := by
    have : (km + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hm1' : env "m" + 1 ≠ 0 := by rw [h_m]; exact hm1
  have ep : intValue? (env "p" + -1 * 1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have ep' : intValue? (env "p" + -1) = some (k - 1) := (intValue?_eq _ _).2 (by rw [h_p]; push_cast; ring)
  have em1 : intValue? (env "m" + 1) = some (km + 1) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have em2 : intValue? (env "m" + 2) = some (km + 2) := (intValue?_eq _ _).2 (by rw [h_m]; push_cast; ring)
  have hBody : ∀ w, Defined Interp.real (Function.update env "x" w) rubi534r91.body →
      0 < (env "d" + env "e" * w ^ 2) ∧ env "f" ≠ 0 ∧ w ≠ 0 := by
    intro w h
    simp [rubi534r91, Defined, eval, Interp.real, hk, hkm, i2, im1, show ¬ k < 0 by omega, show km < 0 by omega] at h
    have hsq : Real.sqrt (env "d" + env "e" * w ^ 2) ≠ 0 := by tauto
    have hle : 0 ≤ (env "d" + env "e" * w ^ 2) := by tauto
    have hlt : 0 < (env "d" + env "e" * w ^ 2) := lt_of_le_of_ne hle (fun h0 => hsq (by rw [← h0, Real.sqrt_zero]))
    first | tauto | (trace_state; sorry)
  obtain ⟨hQ, hf0, ht0⟩ := hBody t hF.self_of_nhds
  have hd0 : env "d" ≠ 0 := by
    intro h0; rw [he, h0] at hQ; simp at hQ
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r91, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    · have hb := hBody w hw
      have hs := Real.sqrt_ne_zero'.2 (hb.1)
      have hle := (hb.1).le
      simp [Defined, eval, Interp.real, hk, i2, im1, ep, ep', em1, em2, show ¬ k - 1 < 0 by omega, show ¬ k < 0 by omega]
      first | done | tauto | (trace_state; sorry)
  · filter_upwards [hF] with w hw
    have hb := hBody w hw
    have hle := (hb.1).le
    simp [rubi534r91, Defined, eval, recEnv, Interp.real, hk, i2, im1, em1, show ¬ k < 0 by omega, hd0, hm1']
    first | done | tauto | (trace_state; sorry)
  · simp only [rubi534r91, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    have hΦ1' : HasDerivAt (Φ "I1") ((env "f" * t) ^ (km + 1) * (env "a" + env "b" * Real.arctan (env "c" * t)) ^ (k - 1) * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ1 using 1; simp [eval, Interp.real, hk, i2, im1, ep, ep', em1]
    have hΦ2' : HasDerivAt (Φ "I2") ((env "f" * t) ^ (km + 2) * (env "a" + env "b" * Real.arctan (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹) t := by
      convert hΦ2 using 1; simp [eval, Interp.real, hk, i2, im1, em2]
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r91.integrals.map (·.1)) Φ "x" w) rubi534r91.result) =
        fun w => (env "f" * w) ^ (km + 1) * Real.sqrt (env "d" + env "e" * w ^ 2) * (env "a" + env "b" * Real.arctan (env "c" * w)) ^ k * (env "d" * env "f" * (env "m" + 1))⁻¹
          + -1 * env "b" * env "c" * env "p" * (env "f" * (env "m" + 1))⁻¹ * Φ "I1" w
          + -1 * env "c" ^ 2 * (env "m" + 2) * (env "f" ^ 2 * (env "m" + 1))⁻¹ * Φ "I2" w := by
      funext w; simp [rubi534r91, eval, recEnv, Interp.real, hk, i2, im1, em1]
      try ring1
    have hEF : eval Interp.real (Function.update env "x" t) rubi534r91.body = (env "f" * t) ^ km * (env "a" + env "b" * Real.arctan (env "c" * t)) ^ k * (Real.sqrt (env "d" + env "e" * t ^ 2))⁻¹ := by
      simp [rubi534r91, eval, Interp.real, hk, hkm, i2, im1]
    rw [hfun, hEF]
    have hft : env "f" * t ≠ 0 := mul_ne_zero hf0 ht0
    have hQd : HasDerivAt (fun w => (env "d" + env "e" * w ^ 2)) (env "e" * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (env "e")).const_add (env "d")
    have hq := hQd.sqrt hQ.ne'
    have hcx : HasDerivAt (fun w => env "c" * w) (env "c") t := by
      simpa using (hasDerivAt_id t).const_mul (env "c")
    have hfx : HasDerivAt (fun w => env "f" * w) (env "f") t := by
      simpa using (hasDerivAt_id t).const_mul (env "f")
    have hM := (((Real.hasDerivAt_arctan' _).comp t hcx).const_mul (env "b")).const_add (env "a")
    have hMk := (hasDerivAt_zpow k _ (Or.inr hk0.le)).comp t hM
    have hX := (hasDerivAt_zpow (km + 1) _ (Or.inl hft)).comp t hfx
    refine (((((hX.mul hq).mul hMk).mul_const _).add (hΦ1'.const_mul _)).add (hΦ2'.const_mul _)).congr_deriv ?_
    simp only [Function.comp_def, Pi.mul_apply, Pi.inv_apply, id, mul_one, add_sub_cancel_right]
    have hD1 : (1 + (env "c" * t) ^ 2) ≠ 0 := (by positivity)
    have hD1' : (1 + env "c" ^ 2 * t ^ 2) ≠ 0 := by rw [show (1 + env "c" ^ 2 * t ^ 2) = (1 + (env "c" * t) ^ 2) by ring]; exact hD1
    have hD1'' : (1 + t ^ 2 * env "c" ^ 2) ≠ 0 := by rw [show (1 + t ^ 2 * env "c" ^ 2) = (1 + (env "c" * t) ^ 2) by ring]; exact hD1
    rw [show (env "a" + env "b" * Real.arctan (env "c" * t)) ^ k = (env "a" + env "b" * Real.arctan (env "c" * t)) ^ (k - 1) * (env "a" + env "b" * Real.arctan (env "c" * t)) by
      rw [← zpow_succ_of' _ _ (by omega)]; congr 1; ring,
      zpow_add₀ hft km 2, zpow_add_one₀ hft km, h_p, h_m]
    have hq2 : Real.sqrt (env "d" + env "e" * t ^ 2) ^ 2 = (env "d" + env "e" * t ^ 2) := Real.sq_sqrt hQ.le
    have hq0 : Real.sqrt (env "d" + env "e" * t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hQ
    generalize Real.arctan (env "c" * t) = AT
    generalize (env "a" + env "b" * AT) ^ (k - 1) = Mk
    generalize (env "f" * t) ^ km = X
    rw [he] at hq2 ⊢
    generalize Real.sqrt (env "d" + (env "c" ^ 2 * env "d") * t ^ 2) = q at hq2 hq0 ⊢
    have hd : env "d" = q ^ 2 / (1 + (env "c" * t) ^ 2) := by
      rw [eq_div_iff hD1]; linear_combination -hq2
    rw [hd]
    push_cast
    have hm1x : 1 + (km : ℝ) ≠ 0 := by rw [add_comm]; exact hm1
    field_simp
    first | ring1 | (push_cast; ring1) | (simp only [Int.cast_add, Int.cast_one]; ring1) | (trace_state; sorry)


end OSR.IntegrationRec137
