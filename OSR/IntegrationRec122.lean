import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of rules not considered before

RUBI rules transcribed as stated.  Each is refuted by an explicit assignment:
the conditions hold and the integrand is defined near a point where the
result or a residual integrand is not (RUBI excludes these cases by its rule
order).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec122

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.3.4 #63 -/
def rubi534r63 : CRule where
  id := "integration.rubi_5_3_4_r63"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:63"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "c") (.int 3))) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "q") (.app2 .mul (.int (-5)) (.pow (.int 2) (.int (-1))))]
  priority := 9701
  description := "RUBI 5.3.4 #63"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:63" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#63"

/-- RUBI 5.3.4 #65 -/
def rubi534r65 : CRule where
  id := "integration.rubi_5_3_4_r65"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:65"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0)]
  priority := 9702
  description := "RUBI 5.3.4 #65"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:65" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#65"

/-- RUBI 5.3.4 #67 -/
def rubi534r67 : CRule where
  id := "integration.rubi_5_3_4_r67"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:67"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 9703
  description := "RUBI 5.3.4 #67"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:67" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#67"

/-- RUBI 5.3.4 #69 -/
def rubi534r69 : CRule where
  id := "integration.rubi_5_3_4_r69"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:69"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.pow (.var "m") (.int 2)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "p") (.int 1)]
  priority := 9704
  description := "RUBI 5.3.4 #69"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:69" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#69"

/-- RUBI 5.3.4 #71 -/
def rubi534r71 : CRule where
  id := "integration.rubi_5_3_4_r71"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:71"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 9705
  description := "RUBI 5.3.4 #71"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:71" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#71"

/-- RUBI 5.3.4 #73 -/
def rubi534r73 : CRule where
  id := "integration.rubi_5_3_4_r73"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:73"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 3)) (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9706
  description := "RUBI 5.3.4 #73"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:73" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#73"

/-- RUBI 5.3.4 #75 -/
def rubi534r75 : CRule where
  id := "integration.rubi_5_3_4_r75"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:75"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "d")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "m") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .ne (.var "m") (.int (-2))]
  priority := 9707
  description := "RUBI 5.3.4 #75"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:75" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#75"

/-- RUBI 5.3.4 #81 -/
def rubi534r81 : CRule where
  id := "integration.rubi_5_3_4_r81"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:81"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "p")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 9708
  description := "RUBI 5.3.4 #81"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:81" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#81"

/-- RUBI 5.3.4 #9 -/
def rubi534r9 : CRule where
  id := "integration.rubi_5_3_4_r9"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "q")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "q") (.int 0)]
  priority := 9709
  description := "RUBI 5.3.4 #9"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:9" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#9"

/-- RUBI 5.3.4 #93 -/
def rubi534r93 : CRule where
  id := "integration.rubi_5_3_4_r93"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:93"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.var "p") (.int (-1))]
  priority := 9710
  description := "RUBI 5.3.4 #93"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:93" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#93"

/-- RUBI 5.3.4 #97 -/
def rubi534r97 : CRule where
  id := "integration.rubi_5_3_4_r97"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:97"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .int (.var "m"),
    .gt (.int (-1)) (.var "q"),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0)]
  priority := 9711
  description := "RUBI 5.3.4 #97"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:97" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#97"

/-- RUBI 5.3.7 #15 -/
def rubi537r15 : CRule where
  id := "integration.rubi_5_3_7_r15"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0)]
  priority := 9712
  description := "RUBI 5.3.7 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:15" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#15"

/-- RUBI 5.3.7 #17 -/
def rubi537r17 : CRule where
  id := "integration.rubi_5_3_7_r17"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9713
  description := "RUBI 5.3.7 #17"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:17" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#17"

/-- RUBI 5.3.7 #21 -/
def rubi537r21 : CRule where
  id := "integration.rubi_5_3_7_r21"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:21"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.pow (.app1 .arctan (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "m"]
  conditions := [.eq (.app2 .add (.var "b") (.pow (.var "c") (.int 2))) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9714
  description := "RUBI 5.3.7 #21"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:21" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#21"

/-- RUBI 5.3.7 #47 -/
def rubi537r47 : CRule where
  id := "integration.rubi_5_3_7_r47"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .arctan (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .arctan (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sech (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b", "e", "f", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 9715
  description := "RUBI 5.3.7 #47"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:47" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#47"

/-- RUBI 5.3.7 #49 -/
def rubi537r49 : CRule where
  id := "integration.rubi_5_3_7_r49"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:49"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .arctan (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .arctan (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sech (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b", "e", "f", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 9716
  description := "RUBI 5.3.7 #49"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent:49" "5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m#49"

/-- RUBI 6.1.11 #3 -/
def rubi6111r3 : CRule where
  id := "integration.rubi_6_1_11_r3"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "n") (.int 2)]
  priority := 9717
  description := "RUBI 6.1.11 #3"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:3" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#3"

/-- RUBI 6.1.11 #4 -/
def rubi6111r4 : CRule where
  id := "integration.rubi_6_1_11_r4"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.var "p")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .mul (.int (-1)) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .mul (.int (-1)) (.var "n")) (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))) (.app2 .add (.var "p") (.int 1)))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))]
  independent := ["a", "b", "c", "d", "n", "p"]
  conditions := [.int (.var "p"),
    .int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .gt (.var "n") (.int 2)]
  priority := 9718
  description := "RUBI 6.1.11 #4"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh:4" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.11 (e x)^m (a+b x^n)^p sinh.m#4"

/-- RUBI 6.1.12 #25 -/
def rubi6112r25 : CRule where
  id := "integration.rubi_6_1_12_r25"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.var "n"))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 9719
  description := "RUBI 6.1.12 #25"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:25" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#25"

/-- RUBI 6.1.12 #26 -/
def rubi6112r26 : CRule where
  id := "integration.rubi_6_1_12_r26"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:26"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "e") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.var "n"))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 9720
  description := "RUBI 6.1.12 #26"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:26" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#26"

/-- RUBI 6.1.12 #31 -/
def rubi6112r31 : CRule where
  id := "integration.rubi_6_1_12_r31"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .int (.var "p"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .gt (.var "p") (.int 1),
    .ne (.var "n") (.int 1)]
  priority := 9721
  description := "RUBI 6.1.12 #31"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:31" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#31"

/-- RUBI 6.1.12 #32 -/
def rubi6112r32 : CRule where
  id := "integration.rubi_6_1_12_r32"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.pow (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "n"),
    .int (.var "p"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .gt (.var "p") (.int 1),
    .ne (.var "n") (.int 1)]
  priority := 9722
  description := "RUBI 6.1.12 #32"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:32" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#32"

/-- RUBI 6.1.12 #35 -/
def rubi6112r35 : CRule where
  id := "integration.rubi_6_1_12_r35"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.var "p") (.int 1),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0)]
  priority := 9723
  description := "RUBI 6.1.12 #35"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:35" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#35"

/-- RUBI 6.1.12 #36 -/
def rubi6112r36 : CRule where
  id := "integration.rubi_6_1_12_r36"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.var "p")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))) (.pow (.var "p") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.var "p") (.int 1),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0)]
  priority := 9724
  description := "RUBI 6.1.12 #36"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:36" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#36"

/-- RUBI 6.1.12 #37 -/
def rubi6112r37 : CRule where
  id := "integration.rubi_6_1_12_r37"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:37"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.var "p") (.int 1),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)]
  priority := 9725
  description := "RUBI 6.1.12 #37"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:37" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#37"

/-- RUBI 6.1.12 #38 -/
def rubi6112r38 : CRule where
  id := "integration.rubi_6_1_12_r38"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.pow (.app2 .add (.var "m") (.int 1)) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.var "p")) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .add (.var "m") (.int 1)) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "n")))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.var "p") (.int 1),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0)]
  priority := 9726
  description := "RUBI 6.1.12 #38"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:38" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#38"

/-- RUBI 6.1.12 #41 -/
def rubi6112r41 : CRule where
  id := "integration.rubi_6_1_12_r41"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:41"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "n")) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "n")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2))]
  priority := 9727
  description := "RUBI 6.1.12 #41"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:41" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#41"

/-- RUBI 6.1.12 #42 -/
def rubi6112r42 : CRule where
  id := "integration.rubi_6_1_12_r42"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.var "n"))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "n") (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 2)) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2))]
  priority := 9728
  description := "RUBI 6.1.12 #42"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:42" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#42"

/-- RUBI 6.1.12 #43 -/
def rubi6112r43 : CRule where
  id := "integration.rubi_6_1_12_r43"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2)),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0)]
  priority := 9729
  description := "RUBI 6.1.12 #43"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:43" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#43"

/-- RUBI 6.1.12 #44 -/
def rubi6112r44 : CRule where
  id := "integration.rubi_6_1_12_r44"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n")))))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1)))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "p") (.int 2)) (.pow (.app2 .add (.var "p") (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "n") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2))))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "n")))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 2)))))]
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.int (.var "m"),
    .int (.var "n"),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2)),
    .gt (.app2 .mul (.int 2) (.var "n")) (.int 0)]
  priority := 9730
  description := "RUBI 6.1.12 #44"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:44" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#44"

/-- RUBI 6.1.12 #65 -/
def rubi6112r65 : CRule where
  id := "integration.rubi_6_1_12_r65"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:65"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 9731
  description := "RUBI 6.1.12 #65"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:65" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#65"

/-- RUBI 6.1.12 #66 -/
def rubi6112r66 : CRule where
  id := "integration.rubi_6_1_12_r66"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:66"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .mul (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "m", "n", "p"]
  conditions := [.eq (.var "m") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))),
    .ne (.var "p") (.int (-1))]
  priority := 9732
  description := "RUBI 6.1.12 #66"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:66" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#66"

/-- RUBI 6.1.12 #67 -/
def rubi6112r67 : CRule where
  id := "integration.rubi_6_1_12_r67"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:67"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "p", "m", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 9733
  description := "RUBI 6.1.12 #67"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:67" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#67"

/-- RUBI 6.1.12 #68 -/
def rubi6112r68 : CRule where
  id := "integration.rubi_6_1_12_r68"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:68"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.var "p"))) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.var "n"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "p", "m", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 9734
  description := "RUBI 6.1.12 #68"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:68" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#68"

/-- RUBI 6.1.13 #10 -/
def rubi6113r10 : CRule where
  id := "integration.rubi_6_1_13_r10"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9735
  description := "RUBI 6.1.13 #10"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:10" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#10"

/-! ## Refutations -/

section
variable {α : Type} [Field α] [CharZero α]
private theorem iv0 : intValue? (0 : α) = some 0 := by simpa using intValue?_intCast (α := α) 0
private theorem iv1 : intValue? (1 : α) = some 1 := by simpa using intValue?_intCast (α := α) 1
private theorem iv2 : intValue? (2 : α) = some 2 := by simpa using intValue?_intCast (α := α) 2
private theorem iv3 : intValue? (3 : α) = some 3 := by simpa using intValue?_intCast (α := α) 3
private theorem iv4 : intValue? (4 : α) = some 4 := by simpa using intValue?_intCast (α := α) 4
private theorem ivm1 : intValue? (-1 : α) = some (-1) := by simpa using intValue?_intCast (α := α) (-1)
private theorem ivm2 : intValue? (-2 : α) = some (-2) := by simpa using intValue?_intCast (α := α) (-2)
private theorem ivm3 : intValue? (-3 : α) = some (-3) := by simpa using intValue?_intCast (α := α) (-3)
private theorem ivm4 : intValue? (-4 : α) = some (-4) := by simpa using intValue?_intCast (α := α) (-4)
private theorem ivm5 : intValue? (-5 : α) = some (-5) := by simpa using intValue?_intCast (α := α) (-5)
private theorem ivm6 : intValue? (-6 : α) = some (-6) := by simpa using intValue?_intCast (α := α) (-6)
private theorem ivm7 : intValue? (-7 : α) = some (-7) := by simpa using intValue?_intCast (α := α) (-7)
private theorem ivm8 : intValue? (-8 : α) = some (-8) := by simpa using intValue?_intCast (α := α) (-8)
private theorem ivm9 : intValue? (-9 : α) = some (-9) := by simpa using intValue?_intCast (α := α) (-9)
private theorem ivm10 : intValue? (-10 : α) = some (-10) := by simpa using intValue?_intCast (α := α) (-10)
private theorem ivm11 : intValue? (-11 : α) = some (-11) := by simpa using intValue?_intCast (α := α) (-11)
private theorem ivm12 : intValue? (-12 : α) = some (-12) := by simpa using intValue?_intCast (α := α) (-12)
private theorem ivnat (n : ℕ) [n.AtLeastTwo] : intValue? (OfNat.ofNat n : α) = some (OfNat.ofNat n) := by
  simpa using intValue?_intCast (α := α) (OfNat.ofNat n : ℤ)
private theorem ivneg (n : ℕ) [n.AtLeastTwo] :
    intValue? (-(OfNat.ofNat n : α)) = some (-(OfNat.ofNat n)) := by
  simpa using intValue?_intCast (α := α) (-(OfNat.ofNat n : ℤ))
end


theorem rubi534r63_counterexample_real : ¬ rubi534r63.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r63.conditions rubi534r63.body rubi534r63.result rubi534r63.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi534r63, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r63, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r63.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r63, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r63, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r65_counterexample_real : ¬ rubi534r65.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r65.conditions rubi534r65.body rubi534r65.result rubi534r65.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r65, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r65.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r65, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r67_counterexample_real : ¬ rubi534r67.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r67.conditions rubi534r67.body rubi534r67.result rubi534r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi534r67, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r67.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r69_counterexample_real : ¬ rubi534r69.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r69.conditions rubi534r69.body rubi534r69.result rubi534r69.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi534r69, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r69, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r69.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r69, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r69, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r71_counterexample_real : ¬ rubi534r71.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r71.conditions rubi534r71.body rubi534r71.result rubi534r71.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi534r71, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r71, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r71.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r71, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r71, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r73_counterexample_real : ¬ rubi534r73.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r73.conditions rubi534r73.body rubi534r73.result rubi534r73.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r73, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r73, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r73.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -2 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r73, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r73, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r75_counterexample_real : ¬ rubi534r75.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r75.conditions rubi534r75.body rubi534r75.result rubi534r75.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" ∨ s = "f" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi534r75, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r75, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi534r75.integrals[0]!, by simp [rubi534r75], ?_⟩
  intro h
  simp [rubi534r75, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi534r81_counterexample_real : ¬ rubi534r81.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r81.conditions rubi534r81.body rubi534r81.result rubi534r81.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi534r81, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r81.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r81, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r9_counterexample_real : ¬ rubi534r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r9.conditions rubi534r9.body rubi534r9.result rubi534r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi534r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r93_counterexample_real : ¬ rubi534r93.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r93.conditions rubi534r93.body rubi534r93.result rubi534r93.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi534r93, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r93, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r93.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r93, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r97_counterexample_real : ¬ rubi534r97.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r97.conditions rubi534r97.body rubi534r97.result rubi534r97.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi534r97, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r97, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r97.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r97, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r97, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi537r15_counterexample_real : ¬ rubi537r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi537r15.conditions rubi537r15.body rubi537r15.result rubi537r15.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (-1 : ℝ) (by simp [rubi537r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi537r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi537r15.integrals[0]!, by simp [rubi537r15], ?_⟩
  intro h
  simp [rubi537r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi537r17_counterexample_real : ¬ rubi537r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi537r17.conditions rubi537r17.body rubi537r17.result rubi537r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi537r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi537r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi537r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi537r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi537r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi537r21_counterexample_real : ¬ rubi537r21.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi537r21.conditions rubi537r21.body rubi537r21.result
  refine not_antiderivHoldsUnder (fun s => if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi537r21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi537r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi537r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi537r47_counterexample_real : ¬ rubi537r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi537r47.conditions rubi537r47.body rubi537r47.result rubi537r47.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi537r47, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi537r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi537r47.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi537r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi537r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi537r49_counterexample_real : ¬ rubi537r49.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi537r49.conditions rubi537r49.body rubi537r49.result rubi537r49.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi537r49, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi537r49, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi537r49.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi537r49, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi537r49, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6111r3_counterexample_real : ¬ rubi6111r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6111r3.conditions rubi6111r3.body rubi6111r3.result rubi6111r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) (1 : ℝ) (by simp [rubi6111r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6111r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6111r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6111r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6111r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6111r3_counterexample_complex : ¬ rubi6111r3.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6111r3.conditions rubi6111r3.body rubi6111r3.result rubi6111r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) (1 : ℂ) (by simp [rubi6111r3, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6111r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6111r3.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6111r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6111r3, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6111r4_counterexample_real : ¬ rubi6111r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6111r4.conditions rubi6111r4.body rubi6111r4.result rubi6111r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) (1 : ℝ) (by simp [rubi6111r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6111r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6111r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6111r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6111r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6111r4_counterexample_complex : ¬ rubi6111r4.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6111r4.conditions rubi6111r4.body rubi6111r4.result rubi6111r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) (1 : ℂ) (by simp [rubi6111r4, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6111r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6111r4.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "p" then -2 else if s = "n" then 3 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6111r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6111r4, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r25_counterexample_real : ¬ rubi6112r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r25.conditions rubi6112r25.body rubi6112r25.result rubi6112r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r25, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r25, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r25_counterexample_complex : ¬ rubi6112r25.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r25.conditions rubi6112r25.body rubi6112r25.result rubi6112r25.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi6112r25, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r25.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r25, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r26_counterexample_real : ¬ rubi6112r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r26.conditions rubi6112r26.body rubi6112r26.result rubi6112r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r26_counterexample_complex : ¬ rubi6112r26.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r26.conditions rubi6112r26.body rubi6112r26.result rubi6112r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi6112r26, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r26.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r26, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r31_counterexample_real : ¬ rubi6112r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r31.conditions rubi6112r31.body rubi6112r31.result rubi6112r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) (0 : ℝ) (by simp [rubi6112r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r31_counterexample_complex : ¬ rubi6112r31.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r31.conditions rubi6112r31.body rubi6112r31.result rubi6112r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) (0 : ℂ) (by simp [rubi6112r31, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r31.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) "x" (0 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r32_counterexample_real : ¬ rubi6112r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r32.conditions rubi6112r32.body rubi6112r32.result rubi6112r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) (0 : ℝ) (by simp [rubi6112r32, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) "x" (0 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r32, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r32_counterexample_complex : ¬ rubi6112r32.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r32.conditions rubi6112r32.body rubi6112r32.result rubi6112r32.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) (0 : ℂ) (by simp [rubi6112r32, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r32, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r32.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" then 1 else if s = "p" then 2 else 0) "x" (0 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r32, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r35_counterexample_real : ¬ rubi6112r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r35.conditions rubi6112r35.body rubi6112r35.result rubi6112r35.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi6112r35, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r35.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r35, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r35_counterexample_complex : ¬ rubi6112r35.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r35.conditions rubi6112r35.body rubi6112r35.result rubi6112r35.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi6112r35, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r35.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r35, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r36_counterexample_real : ¬ rubi6112r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r36.conditions rubi6112r36.body rubi6112r36.result rubi6112r36.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi6112r36, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r36.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r36_counterexample_complex : ¬ rubi6112r36.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r36.conditions rubi6112r36.body rubi6112r36.result rubi6112r36.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi6112r36, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r36, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r36.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r36, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r37_counterexample_real : ¬ rubi6112r37.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r37.conditions rubi6112r37.body rubi6112r37.result rubi6112r37.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi6112r37, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi6112r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r37.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r37, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r37_counterexample_complex : ¬ rubi6112r37.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r37.conditions rubi6112r37.body rubi6112r37.result rubi6112r37.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi6112r37, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi6112r37, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r37.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r37, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r37, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r38_counterexample_real : ¬ rubi6112r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r38.conditions rubi6112r38.body rubi6112r38.result rubi6112r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi6112r38, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi6112r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r38.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r38, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r38_counterexample_complex : ¬ rubi6112r38.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r38.conditions rubi6112r38.body rubi6112r38.result rubi6112r38.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi6112r38, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with w hw; simp [rubi6112r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r38.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -1 else if s = "n" ∨ s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r38, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r41_counterexample_real : ¬ rubi6112r41.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r41.conditions rubi6112r41.body rubi6112r41.result rubi6112r41.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r41, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r41, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r41.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r41, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r41, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r42_counterexample_real : ¬ rubi6112r42.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r42.conditions rubi6112r42.body rubi6112r42.result rubi6112r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r42, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r42.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r42, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r42_counterexample_complex : ¬ rubi6112r42.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r42.conditions rubi6112r42.body rubi6112r42.result rubi6112r42.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi6112r42, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r42.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r42, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r43_counterexample_real : ¬ rubi6112r43.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r43.conditions rubi6112r43.body rubi6112r43.result rubi6112r43.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r43, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r43.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r43, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r44_counterexample_real : ¬ rubi6112r44.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r44.conditions rubi6112r44.body rubi6112r44.result rubi6112r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6112r44, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r44.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r44, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r44_counterexample_complex : ¬ rubi6112r44.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r44.conditions rubi6112r44.body rubi6112r44.result rubi6112r44.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi6112r44, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r44.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "p" then -3 else if s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r44, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r44, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r65_counterexample_real : ¬ rubi6112r65.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi6112r65.conditions rubi6112r65.body rubi6112r65.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi6112r65, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6112r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6112r65_counterexample_complex : ¬ rubi6112r65.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi6112r65.conditions rubi6112r65.body rubi6112r65.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi6112r65, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r65, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6112r65, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6112r66_counterexample_real : ¬ rubi6112r66.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi6112r66.conditions rubi6112r66.body rubi6112r66.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi6112r66, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6112r66, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6112r66_counterexample_complex : ¬ rubi6112r66.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi6112r66.conditions rubi6112r66.body rubi6112r66.result
  refine not_antiderivHoldsUnder (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi6112r66, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6112r66, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6112r67_counterexample_real : ¬ rubi6112r67.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r67.conditions rubi6112r67.body rubi6112r67.result rubi6112r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi6112r67, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r67.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r67_counterexample_complex : ¬ rubi6112r67.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r67.conditions rubi6112r67.body rubi6112r67.result rubi6112r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi6112r67, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r67, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r67.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r67, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r68_counterexample_real : ¬ rubi6112r68.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6112r68.conditions rubi6112r68.body rubi6112r68.result rubi6112r68.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi6112r68, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r68, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r68.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r68, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r68, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6112r68_counterexample_complex : ¬ rubi6112r68.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6112r68.conditions rubi6112r68.body rubi6112r68.result rubi6112r68.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" ∨ s = "p" then 1 else 0) (1 : ℂ) (by simp [rubi6112r68, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6112r68, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6112r68.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6112r68, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6112r68, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r10_counterexample_real : ¬ rubi6113r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r10.conditions rubi6113r10.body rubi6113r10.result rubi6113r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6113r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r10_counterexample_complex : ¬ rubi6113r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r10.conditions rubi6113r10.body rubi6113r10.result rubi6113r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi6113r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec122
