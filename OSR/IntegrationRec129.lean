import OSR.IntegrationRec91

/-!
# Integration (RUBI): rules splitting into residual integrals by linearity

Each result is a combination of residual integrals with constant
coefficients, and the integrand is the same combination of their integrands,
an identity of the polynomial ring once each function application is an
atom.  The residual integrands are built from subterms of the integrand, so
they are defined wherever it is.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec129

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.3.4 #107 -/
def rubi534r107 : CRule where
  id := "integration.rubi_5_3_4_r107"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:107"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q"]
  priority := 10512
  description := "RUBI 5.3.4 #107"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:107" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#107"





/-- RUBI 6.7.7 #33 -/
def rubi677r33 : CRule where
  id := "integration.rubi_6_7_7_r33"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.var "i") (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "i")) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "h") (.app2 .mul (.app2 .mul (.int (-1)) (.var "i")) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "h", "i"]
  conditions := [.eq (.app2 .add (.pow (.var "f") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "g") (.int 2)))) (.int 0),
    .eq (.app2 .add (.pow (.var "h") (.int 2)) (.pow (.var "i") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "g") (.var "h")) (.app2 .mul (.var "f") (.var "i"))) (.int 0)]
  priority := 10518
  description := "RUBI 6.7.7 #33"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:33" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#33"





/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem ti0 (I : Interp ℝ) : I.toInt? (0 : ℝ) = some (0) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti1 (I : Interp ℝ) : I.toInt? (1 : ℝ) = some (1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti2 (I : Interp ℝ) : I.toInt? (2 : ℝ) = some (2) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti3 (I : Interp ℝ) : I.toInt? (3 : ℝ) = some (3) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti4 (I : Interp ℝ) : I.toInt? (4 : ℝ) = some (4) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim1 (I : Interp ℝ) : I.toInt? (-1 : ℝ) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim2 (I : Interp ℝ) : I.toInt? (-2 : ℝ) = some (-2) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim3 (I : Interp ℝ) : I.toInt? (-3 : ℝ) = some (-3) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim4 (I : Interp ℝ) : I.toInt? (-4 : ℝ) = some (-4) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem rubi534r107_holds :
    AntiderivRecHolds Interp.real "x" rubi534r107.conditions rubi534r107.body rubi534r107.result rubi534r107.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r107, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi534r107, Defined, eval, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi534r107, Defined, eval, recEnv, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real]
  · simp only [rubi534r107, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi534r107.integrals.map (·.1)) Φ "x" w) rubi534r107.result) =
        fun w => eval Interp.real env (.var "a") * Φ "I1" w + eval Interp.real env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi534r107, eval, recEnv, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r107, eval, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real, Fn.sec, Fn.csc, Fn.coth, Fn.sech, Fn.csch, Real.tanh_eq_sinh_div_cosh, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    first | ring1 | (field_simp; ring1) | (field_simp; done) | simp

theorem rubi677r33_holds :
    AntiderivRecHolds Interp.real "x" rubi677r33.conditions rubi677r33.body rubi677r33.result rubi677r33.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi677r33, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi677r33, Defined, eval, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi677r33, Defined, eval, recEnv, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real]
  · simp only [rubi677r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval Interp.real (recEnv env (rubi677r33.integrals.map (·.1)) Φ "x" w) rubi677r33.result) =
        fun w => eval Interp.real env (.app2 .mul (.int 2) (.var "i")) * Φ "I1" w + eval Interp.real env (.int 1) * Φ "I2" w := by
      funext w; simp [rubi677r33, eval, recEnv, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi677r33, eval, ti0 Interp.real, ti1 Interp.real, ti2 Interp.real, ti3 Interp.real, ti4 Interp.real, tim1 Interp.real, tim2 Interp.real, tim3 Interp.real, tim4 Interp.real, Interp.real, Fn.sec, Fn.csc, Fn.coth, Fn.sech, Fn.csch, Real.tanh_eq_sinh_div_cosh, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    first | ring1 | (field_simp; ring1) | (field_simp; done) | simp

theorem rubi534r107_real : rubi534r107.Holds .real := rubi534r107_holds
theorem rubi677r33_real : rubi677r33.Holds .real := rubi677r33_holds

end Proofs

end OSR.IntegrationRec129
