import OSR.IntegrationRec91

/-!
# Integration (RUBI): a linear split over `√(a + c x⁴)`

1.2.2.3 #25 splits `(d + e x²)/√(a + c x⁴)` by linearity.  Proved over ℝ
(`arith1#root` has no complex interpretation in the fragment).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec160

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 1.2.2.3 #25 -/
def rubi1223r25 : CRule where
  id := "integration.rubi_1_2_2_3_r25"; legacyId := some "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "c") (.pow (.var "x") (.int 4)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "c", "d", "e"]
  conditions := [.gt (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.int 0)]
  priority := 11890
  description := "RUBI 1.2.2.3 #25"
  provenance := migrated "rubi:1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p:25" "1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p.m#25"

/-! ## Proofs -/

theorem rubi1223r25_real : rubi1223r25.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi1223r25.conditions rubi1223r25.body rubi1223r25.result rubi1223r25.integrals
  intro env hc t hF
  have i2 : intValue? (2 : ℝ) = some 2 := (intValue?_eq _ _).2 (by norm_num)
  have i4 : intValue? (4 : ℝ) = some 4 := (intValue?_eq _ _).2 (by norm_num)
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi1223r25, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi1223r25, Defined, eval, Interp.real, i2, i4, im1] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi1223r25, Defined, eval, recEnv]
  · simp only [rubi1223r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi1223r25, eval, recEnv, Interp.real, i2, i4, im1] at hΦ1 hΦ2 ⊢
    refine ((hΦ1.const_mul (env "d")).add (hΦ2.const_mul (env "e"))).congr_deriv ?_
    ring

end OSR.IntegrationRec160
