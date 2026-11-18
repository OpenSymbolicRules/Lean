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

namespace OSR.IntegrationRec128

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.4 #140 -/
def rubi734r140 : CRule where
  id := "integration.rubi_7_3_4_r140"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:140"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10401
  description := "RUBI 7.3.4 #140"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:140" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#140"

/-- RUBI 5.3.4 #41 -/
def rubi534r41 : CRule where
  id := "integration.rubi_5_3_4_r41"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 10402
  description := "RUBI 5.3.4 #41"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:41" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#41"

/-- RUBI 7.3.4 #41 -/
def rubi734r41 : CRule where
  id := "integration.rubi_7_3_4_r41"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 10403
  description := "RUBI 7.3.4 #41"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:41" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#41"

/-- RUBI 7.3.4 #138 -/
def rubi734r138 : CRule where
  id := "integration.rubi_7_3_4_r138"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:138"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 10404
  description := "RUBI 7.3.4 #138"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:138" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#138"

/-- RUBI 5.3.4 #140 -/
def rubi534r140 : CRule where
  id := "integration.rubi_5_3_4_r140"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:140"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10405
  description := "RUBI 5.3.4 #140"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:140" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#140"

/-- RUBI 7.3.4 #132 -/
def rubi734r132 : CRule where
  id := "integration.rubi_7_3_4_r132"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:132"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  priority := 10406
  description := "RUBI 7.3.4 #132"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:132" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#132"

/-- RUBI 5.3.4 #138 -/
def rubi534r138 : CRule where
  id := "integration.rubi_5_3_4_r138"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:138"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 10407
  description := "RUBI 5.3.4 #138"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:138" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#138"

/-- RUBI 5.3.4 #132 -/
def rubi534r132 : CRule where
  id := "integration.rubi_5_3_4_r132"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:132"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  priority := 10408
  description := "RUBI 5.3.4 #132"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:132" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#132"

/-- RUBI 7.3.1 #160 -/
def rubi731r160 : CRule where
  id := "integration.rubi_7_3_1_r160"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:160"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 10409
  description := "RUBI 7.3.1 #160"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:160" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#160"

/-- RUBI 7.3.1 #61 -/
def rubi731r61 : CRule where
  id := "integration.rubi_7_3_1_r61"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 10410
  description := "RUBI 7.3.1 #61"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:61" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#61"

/-- RUBI 7.3.1 #158 -/
def rubi731r158 : CRule where
  id := "integration.rubi_7_3_1_r158"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:158"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 10411
  description := "RUBI 7.3.1 #158"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:158" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#158"

/-- RUBI 7.3.1 #152 -/
def rubi731r152 : CRule where
  id := "integration.rubi_7_3_1_r152"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:152"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "d") (.pow (.var "x") (.var "m")))) (.app1 .arctanh (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  priority := 10412
  description := "RUBI 7.3.1 #152"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:152" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#152"

/-! ## Proofs -/

section Proofs

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

private theorem ti0 (I : Interp 𝕜) : I.toInt? (0 : 𝕜) = some (0) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti1 (I : Interp 𝕜) : I.toInt? (1 : 𝕜) = some (1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti2 (I : Interp 𝕜) : I.toInt? (2 : 𝕜) = some (2) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti3 (I : Interp 𝕜) : I.toInt? (3 : 𝕜) = some (3) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem ti4 (I : Interp 𝕜) : I.toInt? (4 : 𝕜) = some (4) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim1 (I : Interp 𝕜) : I.toInt? (-1 : 𝕜) = some (-1) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim2 (I : Interp 𝕜) : I.toInt? (-2 : 𝕜) = some (-2) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim3 (I : Interp 𝕜) : I.toInt? (-3 : 𝕜) = some (-3) :=
  (I.toInt?_eq _ _).2 (by simp)

private theorem tim4 (I : Interp 𝕜) : I.toInt? (-4 : 𝕜) = some (-4) :=
  (I.toInt?_eq _ _).2 (by simp)

theorem rubi734r140_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi734r140.conditions rubi734r140.body rubi734r140.result rubi734r140.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r140, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi734r140, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi734r140, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi734r140, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi734r140.integrals.map (·.1)) Φ "x" w) rubi734r140.result) =
        fun w => eval I env (.var "d") * Φ "I1" w + eval I env (.var "e") * Φ "I2" w := by
      funext w; simp [rubi734r140, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r140, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi534r41_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi534r41.conditions rubi534r41.body rubi534r41.result rubi534r41.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi534r41, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi534r41, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi534r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi534r41.integrals.map (·.1)) Φ "x" w) rubi534r41.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi534r41, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r41, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi734r41_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi734r41.conditions rubi734r41.body rubi734r41.result rubi734r41.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r41, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi734r41, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi734r41, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi734r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi734r41.integrals.map (·.1)) Φ "x" w) rubi734r41.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi734r41, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r41, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi734r138_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi734r138.conditions rubi734r138.body rubi734r138.result rubi734r138.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r138, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi734r138, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi734r138, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi734r138, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi734r138.integrals.map (·.1)) Φ "x" w) rubi734r138.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi734r138, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r138, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi534r140_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi534r140.conditions rubi534r140.body rubi534r140.result rubi534r140.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r140, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi534r140, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi534r140, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi534r140, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi534r140.integrals.map (·.1)) Φ "x" w) rubi534r140.result) =
        fun w => eval I env (.var "d") * Φ "I1" w + eval I env (.var "e") * Φ "I2" w := by
      funext w; simp [rubi534r140, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r140, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi734r132_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi734r132.conditions rubi734r132.body rubi734r132.result rubi734r132.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r132, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi734r132, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi734r132, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi734r132, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi734r132.integrals.map (·.1)) Φ "x" w) rubi734r132.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi734r132, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi734r132, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi534r138_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi534r138.conditions rubi534r138.body rubi534r138.result rubi534r138.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r138, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi534r138, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi534r138, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi534r138, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi534r138.integrals.map (·.1)) Φ "x" w) rubi534r138.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi534r138, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r138, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi534r132_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi534r132.conditions rubi534r132.body rubi534r132.result rubi534r132.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi534r132, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi534r132, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi534r132, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi534r132, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi534r132.integrals.map (·.1)) Φ "x" w) rubi534r132.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi534r132, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi534r132, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi731r160_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi731r160.conditions rubi731r160.body rubi731r160.result rubi731r160.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r160, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi731r160, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi731r160, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi731r160, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi731r160.integrals.map (·.1)) Φ "x" w) rubi731r160.result) =
        fun w => eval I env (.var "d") * Φ "I1" w + eval I env (.var "e") * Φ "I2" w := by
      funext w; simp [rubi731r160, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r160, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi731r61_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi731r61.conditions rubi731r61.body rubi731r61.result rubi731r61.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r61, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi731r61, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi731r61, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi731r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi731r61.integrals.map (·.1)) Φ "x" w) rubi731r61.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi731r61, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r61, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi731r158_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi731r158.conditions rubi731r158.body rubi731r158.result rubi731r158.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r158, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi731r158, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi731r158, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi731r158, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi731r158.integrals.map (·.1)) Φ "x" w) rubi731r158.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi731r158, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r158, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi731r152_holds (I : Interp 𝕜) :
    AntiderivRecHolds I "x" rubi731r152.conditions rubi731r152.body rubi731r152.result rubi731r152.integrals := by
  intro env hc t hF
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r152, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> filter_upwards [hF] with w hw <;> simp [rubi731r152, Defined, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4] at hw ⊢ <;> tauto
  · exact Eventually.of_forall fun w => by simp [rubi731r152, Defined, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
  · simp only [rubi731r152, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨h1, h2⟩ := hΦ
    have hfun : (fun w => eval I (recEnv env (rubi731r152.integrals.map (·.1)) Φ "x" w) rubi731r152.result) =
        fun w => eval I env (.var "a") * Φ "I1" w + eval I env (.var "b") * Φ "I2" w := by
      funext w; simp [rubi731r152, eval, recEnv, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    rw [hfun]
    refine ((h1.const_mul _).add (h2.const_mul _)).congr_deriv ?_
    simp [rubi731r152, eval, ti0, ti1, ti2, ti3, ti4, tim1, tim2, tim3, tim4]
    try ring

theorem rubi734r140_real : rubi734r140.Holds .real := rubi734r140_holds Interp.real
theorem rubi534r41_real : rubi534r41.Holds .real := rubi534r41_holds Interp.real
theorem rubi534r41_complex : rubi534r41.Holds .complex := rubi534r41_holds Interp.complex
theorem rubi734r41_real : rubi734r41.Holds .real := rubi734r41_holds Interp.real
theorem rubi734r138_real : rubi734r138.Holds .real := rubi734r138_holds Interp.real
theorem rubi534r140_real : rubi534r140.Holds .real := rubi534r140_holds Interp.real
theorem rubi534r140_complex : rubi534r140.Holds .complex := rubi534r140_holds Interp.complex
theorem rubi734r132_real : rubi734r132.Holds .real := rubi734r132_holds Interp.real
theorem rubi534r138_real : rubi534r138.Holds .real := rubi534r138_holds Interp.real
theorem rubi534r138_complex : rubi534r138.Holds .complex := rubi534r138_holds Interp.complex
theorem rubi534r132_real : rubi534r132.Holds .real := rubi534r132_holds Interp.real
theorem rubi534r132_complex : rubi534r132.Holds .complex := rubi534r132_holds Interp.complex
theorem rubi731r160_real : rubi731r160.Holds .real := rubi731r160_holds Interp.real
theorem rubi731r61_real : rubi731r61.Holds .real := rubi731r61_holds Interp.real
theorem rubi731r158_real : rubi731r158.Holds .real := rubi731r158_holds Interp.real
theorem rubi731r152_real : rubi731r152.Holds .real := rubi731r152_holds Interp.real

end Proofs

end OSR.IntegrationRec128
