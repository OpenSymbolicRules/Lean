import OSR.IntegrationRec91

/-!
# Integration (RUBI): more linear splits into residual integrals

Rules whose result is a combination, with coefficients free of `x`, of
residual integrals: partial fractions in `sin` and `tan`, and splits of
`(a + b arccoth(c x)) u`, `(A + C tan²)/tan` and `(c + d csc) √(a + b csc)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec181

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.1.2.1 #14 -/
def rubi4121r14 : CRule where
  id := "integration.rubi_4_1_2_1_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 15000
  description := "RUBI 4.1.2.1 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:14" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#14"

/-- RUBI 4.3.2.1 #29 -/
def rubi4321r29 : CRule where
  id := "integration.rubi_4_3_2_1_r29"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 15001
  description := "RUBI 4.3.2.1 #29"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:29" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#29"

/-- RUBI 4.3.4.1 #9 -/
def rubi4341r9 : CRule where
  id := "integration.rubi_4_3_4_1_r9"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "A") (.var "I1")) (.app2 .mul (.var "C") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int (-1))))),
    ("I2", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))]
  independent := ["e", "f", "A", "C"]
  conditions := [.ne (.var "A") (.var "C")]
  priority := 15002
  description := "RUBI 4.3.4.1 #9"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):9" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#9"

/-- RUBI 4.5.2.1 #13 -/
def rubi4521r13 : CRule where
  id := "integration.rubi_4_5_2_1_r13"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.var "c") (.var "I1")) (.app2 .mul (.var "d") (.var "I2")))
  integrals := [("I1", (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))),
    ("I2", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 15003
  description := "RUBI 4.5.2.1 #13"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:13" "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#13"

/-- RUBI 4.5.2.1 #19 -/
def rubi4521r19 : CRule where
  id := "integration.rubi_4_5_2_1_r19"; legacyId := some "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "c") (.var "I1")) (.app2 .mul (.var "d") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csc (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 15004
  description := "RUBI 4.5.2.1 #19"
  provenance := migrated "rubi:4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n:19" "4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m#19"

/-- RUBI 7.3.1 #159 -/
def rubi731r159 : CRule where
  id := "integration.rubi_7_3_1_r159"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:159"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 15005
  description := "RUBI 7.3.1 #159"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:159" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#159"

/-- RUBI 7.3.1 #161 -/
def rubi731r161 : CRule where
  id := "integration.rubi_7_3_1_r161"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:161"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 15006
  description := "RUBI 7.3.1 #161"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:161" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#161"

/-- RUBI 7.3.1 #62 -/
def rubi731r62 : CRule where
  id := "integration.rubi_7_3_1_r62"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:62"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 15007
  description := "RUBI 7.3.1 #62"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p:62" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 u (a+b arctanh(c x^n))^p.m#62"

/-- RUBI 7.3.4 #139 -/
def rubi734r139 : CRule where
  id := "integration.rubi_7_3_4_r139"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:139"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "f", "g"]
  priority := 15008
  description := "RUBI 7.3.4 #139"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:139" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#139"

/-- RUBI 7.3.4 #141 -/
def rubi734r141 : CRule where
  id := "integration.rubi_7_3_4_r141"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:141"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "d") (.var "I1")) (.app2 .mul (.var "e") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.var "x") (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1))))))) (.pow (.var "x") (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  priority := 15009
  description := "RUBI 7.3.4 #141"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:141" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#141"

/-- RUBI 7.3.4 #42 -/
def rubi734r42 : CRule where
  id := "integration.rubi_7_3_4_r42"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.var "b") (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .arctanh (.pow (.app2 .mul (.var "c") (.var "x")) (.int (-1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  priority := 15010
  description := "RUBI 7.3.4 #42"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:42" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#42"

theorem rubi4121r14_real : rubi4121r14.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4121r14.conditions rubi4121r14.body rubi4121r14.result rubi4121r14.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4121r14, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r14, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4121r14, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4121r14, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4121r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4121r14, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4121r14_complex : rubi4121r14.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4121r14.conditions rubi4121r14.body rubi4121r14.result rubi4121r14.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4121r14, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4121r14, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4121r14, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4121r14, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4121r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4121r14, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4321r29_real : rubi4321r29.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4321r29.conditions rubi4321r29.body rubi4321r29.result rubi4321r29.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r29, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r29, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r29, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r29, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4321r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4321r29, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4321r29_complex : rubi4321r29.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4321r29.conditions rubi4321r29.body rubi4321r29.result rubi4321r29.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4321r29, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4321r29, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4321r29, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4321r29, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4321r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4321r29, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4341r9_real : rubi4341r9.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4341r9.conditions rubi4341r9.body rubi4341r9.result rubi4341r9.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r9, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r9, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r9, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r9, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4341r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4341r9, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4341r9_complex : rubi4341r9.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi4341r9.conditions rubi4341r9.body rubi4341r9.result rubi4341r9.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4341r9, Defined, eval, Interp.complex, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4341r9, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4341r9, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4341r9, Defined, eval, recEnv, Interp.complex, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4341r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4341r9, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Complex.sin_add (env "c")] <;> ring1)
      | (rw [Complex.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4521r13_real : rubi4521r13.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4521r13.conditions rubi4521r13.body rubi4521r13.result rubi4521r13.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4521r13, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4521r13, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4521r13, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4521r13, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4521r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4521r13, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi4521r19_real : rubi4521r19.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi4521r19.conditions rubi4521r19.body rubi4521r19.result rubi4521r19.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi4521r19, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi4521r19, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi4521r19, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi4521r19, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi4521r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi4521r19, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi731r159_real : rubi731r159.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r159.conditions rubi731r159.body rubi731r159.result rubi731r159.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi731r159, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r159, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi731r159, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi731r159, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi731r159, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi731r159, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi731r161_real : rubi731r161.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r161.conditions rubi731r161.body rubi731r161.result rubi731r161.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi731r161, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r161, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi731r161, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi731r161, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi731r161, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi731r161, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi731r62_real : rubi731r62.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi731r62.conditions rubi731r62.body rubi731r62.result rubi731r62.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi731r62, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi731r62, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi731r62, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi731r62, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi731r62, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi731r62, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi734r139_real : rubi734r139.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r139.conditions rubi734r139.body rubi734r139.result rubi734r139.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi734r139, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r139, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi734r139, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi734r139, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi734r139, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi734r139, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi734r141_real : rubi734r141.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r141.conditions rubi734r141.body rubi734r141.result rubi734r141.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi734r141, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r141, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi734r141, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi734r141, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi734r141, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi734r141, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

theorem rubi734r42_real : rubi734r42.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi734r42.conditions rubi734r42.body rubi734r42.result rubi734r42.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have hF0 := hF.self_of_nhds
  simp [rubi734r42, Defined, eval, Interp.real, i2, im1, Cond.Holds] at hc hF0
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi734r42, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi734r42, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by
      simp [rubi734r42, Defined, eval, recEnv, Interp.real, i2, im1] <;> first | tauto | (trace_state; sorry)
  · simp only [rubi734r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi734r42, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)
        | exact (hΦ1.const_mul _).sub (hΦ2.const_mul _)
        | exact (hΦ1.mul_const _).add (hΦ2.mul_const _)
        | (trace_state; sorry)) ?_
    first
      | ring1
      | ((try casesm* _ ∧ _); field_simp <;> ring1)
      | (simp only [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_eq_zero_iff, not_or] at *; (try casesm* _ ∧ _); field_simp <;> ring1)
      | (rw [Real.sin_add (env "c")] <;> ring1)
      | (rw [Real.cos_add (env "c")] <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp <;> ring1)
      | ((try obtain ⟨h1, h2⟩ := hF0); field_simp
         first
           | linear_combination (mul_inv_cancel₀ hc)
           | linear_combination (mul_inv_cancel₀ hc.1)
           | linear_combination (mul_inv_cancel₀ hc.2)
           | linear_combination (mul_inv_cancel₀ hc.2.1)
           | linear_combination (mul_inv_cancel₀ hc.2.2))
      | (trace_state; sorry)

end OSR.IntegrationRec181
