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

namespace OSR.IntegrationRec126

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 7.3.3 #3 -/
def rubi733r3 : CRule where
  id := "integration.rubi_7_3_3_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int (-1)))))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.pow (.var "e") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int (-1)))))) (.pow (.var "e") (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int (-1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .ln (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "d")) (.var "e")) (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int (-1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 10101
  description := "RUBI 7.3.3 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p:3" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p.m#3"

/-- RUBI 7.3.3 #9 -/
def rubi733r9 : CRule where
  id := "integration.rubi_7_3_3_r9"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.ne (.var "q") (.int (-1))]
  priority := 10102
  description := "RUBI 7.3.3 #9"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p:9" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p.m#9"

/-- RUBI 7.3.4 #15 -/
def rubi734mr15 : CRule where
  id := "integration.rubi_7_3_4_misc_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2))]
  priority := 10103
  description := "RUBI 7.3.4 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:15" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#15"

/-- RUBI 7.3.4 #17 -/
def rubi734mr17 : CRule where
  id := "integration.rubi_7_3_4_misc_r17"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2)),
    .ne (.var "m") (.int (-1))]
  priority := 10104
  description := "RUBI 7.3.4 #17"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:17" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#17"

/-- RUBI 7.3.4 #21 -/
def rubi734mr21 : CRule where
  id := "integration.rubi_7_3_4_misc_r21"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:21"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "m")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.pow (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "m"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2)),
    .ne (.var "m") (.int (-1))]
  priority := 10105
  description := "RUBI 7.3.4 #21"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:21" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#21"

/-- RUBI 7.3.4 #45 -/
def rubi734mr45 : CRule where
  id := "integration.rubi_7_3_4_misc_r45"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .arctanh (.app1 .tan (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sec (.app2 .add (.app2 .mul (.int 2) (.var "a")) (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "x"))))))]
  independent := ["a", "b", "e", "f", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 10106
  description := "RUBI 7.3.4 #45"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent:45" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m#45"

/-- RUBI 7.3.4 #1 -/
def rubi734r1 : CRule where
  id := "integration.rubi_7_3_4_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "f")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 0)]
  priority := 10107
  description := "RUBI 7.3.4 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:1" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#1"

/-- RUBI 7.3.4 #103 -/
def rubi734r103 : CRule where
  id := "integration.rubi_7_3_4_r103"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:103"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.ne (.var "q") (.int (-1))]
  priority := 10108
  description := "RUBI 7.3.4 #103"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:103" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#103"

/-- RUBI 7.3.4 #11 -/
def rubi734r11 : CRule where
  id := "integration.rubi_7_3_4_r11"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "q")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "d")) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "q") (.int 0),
    .gt (.var "p") (.int 1)]
  priority := 10109
  description := "RUBI 7.3.4 #11"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:11" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#11"

/-- RUBI 7.3.4 #115 -/
def rubi734r115 : CRule where
  id := "integration.rubi_7_3_4_r115"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:115"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "f") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "g") (.int 2)))) (.int 0)]
  priority := 10110
  description := "RUBI 7.3.4 #115"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:115" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#115"

/-- RUBI 7.3.4 #144 -/
def rubi734r144 : CRule where
  id := "integration.rubi_7_3_4_r144"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:144"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.int 2)))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2)))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.int 2))) (.pow (.app2 .mul (.int 2) (.var "g")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.var "x") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.int 2))) (.pow (.int 2) (.int (-1))))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "c") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "e")) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "f")) (.var "g")) (.int 0)]
  priority := 10111
  description := "RUBI 7.3.4 #144"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:144" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#144"

/-- RUBI 7.3.4 #15 -/
def rubi734r15 : CRule where
  id := "integration.rubi_7_3_4_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:15"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 10112
  description := "RUBI 7.3.4 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:15" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#15"

/-- RUBI 7.3.4 #23 -/
def rubi734r23 : CRule where
  id := "integration.rubi_7_3_4_r23"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.int 2) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 10113
  description := "RUBI 7.3.4 #23"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:23" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#23"

/-- RUBI 7.3.4 #27 -/
def rubi734r27 : CRule where
  id := "integration.rubi_7_3_4_r27"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "c")) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "q") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 10114
  description := "RUBI 7.3.4 #27"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:27" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#27"

/-- RUBI 7.3.4 #3 -/
def rubi734r3 : CRule where
  id := "integration.rubi_7_3_4_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.app1 .ln (.app2 .add (.int 2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1))))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .ln (.app2 .add (.int 2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2)))) (.int 0)]
  priority := 10115
  description := "RUBI 7.3.4 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:3" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#3"

/-- RUBI 7.3.4 #31 -/
def rubi734r31 : CRule where
  id := "integration.rubi_7_3_4_r31"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "c")) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 4) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "p") (.int 1),
    .ne (.var "q") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 10116
  description := "RUBI 7.3.4 #31"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:31" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#31"

/-- RUBI 7.3.4 #33 -/
def rubi734r33 : CRule where
  id := "integration.rubi_7_3_4_r33"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "q"),
    .gt (.int (-1)) (.var "p")]
  priority := 10117
  description := "RUBI 7.3.4 #33"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:33" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#33"

/-- RUBI 7.3.4 #45 -/
def rubi734r45 : CRule where
  id := "integration.rubi_7_3_4_r45"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "f") (.int 2))) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 10118
  description := "RUBI 7.3.4 #45"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:45" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#45"

/-- RUBI 7.3.4 #47 -/
def rubi734r47 : CRule where
  id := "integration.rubi_7_3_4_r47"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 10119
  description := "RUBI 7.3.4 #47"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:47" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#47"

/-- RUBI 7.3.4 #49 -/
def rubi734r49 : CRule where
  id := "integration.rubi_7_3_4_r49"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:49"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "c") (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "p"),
    .gt (.var "p") (.int 0)]
  priority := 10120
  description := "RUBI 7.3.4 #49"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:49" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#49"

/-- RUBI 7.3.4 #53 -/
def rubi734r53 : CRule where
  id := "integration.rubi_7_3_4_r53"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:53"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 10121
  description := "RUBI 7.3.4 #53"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:53" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#53"

/-- RUBI 7.3.4 #55 -/
def rubi734r55 : CRule where
  id := "integration.rubi_7_3_4_r55"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:55"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 10122
  description := "RUBI 7.3.4 #55"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:55" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#55"

/-- RUBI 7.3.4 #59 -/
def rubi734r59 : CRule where
  id := "integration.rubi_7_3_4_r59"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0),
    .ne (.var "q") (.int (-1))]
  priority := 10123
  description := "RUBI 7.3.4 #59"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:59" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#59"

/-- RUBI 7.3.4 #61 -/
def rubi734r61 : CRule where
  id := "integration.rubi_7_3_4_r61"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int 4) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2))]
  priority := 10124
  description := "RUBI 7.3.4 #61"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:61" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#61"

/-- RUBI 7.3.4 #63 -/
def rubi734r63 : CRule where
  id := "integration.rubi_7_3_4_r63"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:63"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "c") (.int 3))) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "q") (.app2 .mul (.int (-5)) (.pow (.int 2) (.int (-1))))]
  priority := 10125
  description := "RUBI 7.3.4 #63"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:63" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#63"

/-- RUBI 7.3.4 #65 -/
def rubi734r65 : CRule where
  id := "integration.rubi_7_3_4_r65"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:65"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.pow (.var "c") (.int 3))) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.pow (.var "c") (.int 2))) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0)]
  priority := 10126
  description := "RUBI 7.3.4 #65"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:65" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#65"

/-- RUBI 7.3.4 #67 -/
def rubi734r67 : CRule where
  id := "integration.rubi_7_3_4_r67"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:67"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "c") (.var "d")) (.pow (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "q")]
  priority := 10127
  description := "RUBI 7.3.4 #67"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:67" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#67"

/-- RUBI 7.3.4 #71 -/
def rubi734r71 : CRule where
  id := "integration.rubi_7_3_4_r71"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:71"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "q", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 10128
  description := "RUBI 7.3.4 #71"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:71" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#71"

/-- RUBI 7.3.4 #75 -/
def rubi734r75 : CRule where
  id := "integration.rubi_7_3_4_r75"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:75"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "d")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "m") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .ne (.var "m") (.int (-2))]
  priority := 10129
  description := "RUBI 7.3.4 #75"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:75" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#75"

/-- RUBI 7.3.4 #81 -/
def rubi734r81 : CRule where
  id := "integration.rubi_7_3_4_r81"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:81"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "p")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "p") (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 10130
  description := "RUBI 7.3.4 #81"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:81" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#81"

/-- RUBI 7.3.4 #9 -/
def rubi734r9 : CRule where
  id := "integration.rubi_7_3_4_r9"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "q")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "q") (.int 0)]
  priority := 10131
  description := "RUBI 7.3.4 #9"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:9" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#9"

/-- RUBI 7.3.4 #93 -/
def rubi734r93 : CRule where
  id := "integration.rubi_7_3_4_r93"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:93"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "p"),
    .int (.app2 .mul (.int 2) (.var "q")),
    .gt (.int (-1)) (.var "q"),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.var "p") (.int (-1))]
  priority := 10132
  description := "RUBI 7.3.4 #93"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:93" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#93"

/-- RUBI 7.3.4 #97 -/
def rubi734r97 : CRule where
  id := "integration.rubi_7_3_4_r97"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:97"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "p", "q"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "q"),
    .gt (.int (-1)) (.var "p"),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "q"))) (.int 2)) (.int 0)]
  priority := 10133
  description := "RUBI 7.3.4 #97"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p:97" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 u (a+b arctanh(c x))^p.m#97"

/-- RUBI 7.3.5 #7 -/
def rubi735r7 : CRule where
  id := "integration.rubi_7_3_5_r7"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.5 u (a+b arctanh(c+d x))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "p"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "p")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 10134
  description := "RUBI 7.3.5 #7"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.5 u (a+b arctanh(c+d x))^p:7" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.5 u (a+b arctanh(c+d x))^p.m#7"

/-- RUBI 7.3.7 #15 -/
def rubi737r15 : CRule where
  id := "integration.rubi_7_3_7_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.var "x") (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .arctanh (.app2 .mul (.app2 .mul (.var "c") (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app1 .ln (.var "x")) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c"]
  conditions := [.eq (.var "b") (.pow (.var "c") (.int 2))]
  priority := 10135
  description := "RUBI 7.3.7 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent:15" "7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.7 Miscellaneous inverse hyperbolic tangent.m#15"

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


theorem rubi733r3_counterexample_real : ¬ rubi733r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi733r3.conditions rubi733r3.body rubi733r3.result rubi733r3.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi733r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi733r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi733r3.integrals[1]!, by simp [rubi733r3], ?_⟩
  intro h
  simp [rubi733r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi733r9_counterexample_real : ¬ rubi733r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi733r9.conditions rubi733r9.body rubi733r9.result rubi733r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi733r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi733r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi733r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi733r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi733r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734mr15_counterexample_real : ¬ rubi734mr15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734mr15.conditions rubi734mr15.body rubi734mr15.result rubi734mr15.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (-1 : ℝ) (by simp [rubi734mr15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi734mr15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi734mr15.integrals[0]!, by simp [rubi734mr15], ?_⟩
  intro h
  simp [rubi734mr15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi734mr17_counterexample_real : ¬ rubi734mr17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734mr17.conditions rubi734mr17.body rubi734mr17.result rubi734mr17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi734mr17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734mr17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734mr17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734mr17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734mr17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734mr21_counterexample_real : ¬ rubi734mr21.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi734mr21.conditions rubi734mr21.body rubi734mr21.result
  refine not_antiderivHoldsUnder (fun s => if s = "a" then 1 else 0) (1 : ℝ) (by simp [rubi734mr21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734mr21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi734mr21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi734mr45_counterexample_real : ¬ rubi734mr45.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734mr45.conditions rubi734mr45.body rubi734mr45.result rubi734mr45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "e" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi734mr45, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734mr45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734mr45.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "e" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734mr45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734mr45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r1_counterexample_real : ¬ rubi734r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r1.conditions rubi734r1.body rubi734r1.result rubi734r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r103_counterexample_real : ¬ rubi734r103.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r103.conditions rubi734r103.body rubi734r103.result rubi734r103.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi734r103, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r103.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r103, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r11_counterexample_real : ¬ rubi734r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r11.conditions rubi734r11.body rubi734r11.result rubi734r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi734r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r115_counterexample_real : ¬ rubi734r115.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r115.conditions rubi734r115.body rubi734r115.result rubi734r115.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r115, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r115, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r115.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r115, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r115, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r144_counterexample_real : ¬ rubi734r144.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r144.conditions rubi734r144.body rubi734r144.result rubi734r144.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) (1 : ℝ) (by simp [rubi734r144, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r144, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r144.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "e" ∨ s = "f" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r144, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r144, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r15_counterexample_real : ¬ rubi734r15.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi734r15.conditions rubi734r15.body rubi734r15.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi734r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi734r23_counterexample_real : ¬ rubi734r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r23.conditions rubi734r23.body rubi734r23.result rubi734r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r23, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r27_counterexample_real : ¬ rubi734r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r27.conditions rubi734r27.body rubi734r27.result rubi734r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi734r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r3_counterexample_real : ¬ rubi734r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r3.conditions rubi734r3.body rubi734r3.result rubi734r3.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi734r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi734r3.integrals[0]!, by simp [rubi734r3], ?_⟩
  intro h
  simp [rubi734r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi734r31_counterexample_real : ¬ rubi734r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r31.conditions rubi734r31.body rubi734r31.result rubi734r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi734r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r33_counterexample_real : ¬ rubi734r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r33.conditions rubi734r33.body rubi734r33.result rubi734r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else 0) (1 : ℝ) (by simp [rubi734r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r45_counterexample_real : ¬ rubi734r45.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r45.conditions rubi734r45.body rubi734r45.result rubi734r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi734r45, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r45.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r47_counterexample_real : ¬ rubi734r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r47.conditions rubi734r47.body rubi734r47.result rubi734r47.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r47, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi734r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r47.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "e" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r49_counterexample_real : ¬ rubi734r49.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r49.conditions rubi734r49.body rubi734r49.result rubi734r49.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r49, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r49, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r49.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r49, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r49, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r53_counterexample_real : ¬ rubi734r53.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r53.conditions rubi734r53.body rubi734r53.result rubi734r53.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r53, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi734r53, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r53.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r53, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r53, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r55_counterexample_real : ¬ rubi734r55.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r55.conditions rubi734r55.body rubi734r55.result rubi734r55.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi734r55, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r55.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r59_counterexample_real : ¬ rubi734r59.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r59.conditions rubi734r59.body rubi734r59.result rubi734r59.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi734r59, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r59.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r61_counterexample_real : ¬ rubi734r61.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r61.conditions rubi734r61.body rubi734r61.result rubi734r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi734r61, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r61.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r63_counterexample_real : ¬ rubi734r63.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r63.conditions rubi734r63.body rubi734r63.result rubi734r63.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi734r63, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r63, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r63.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r63, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r63, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r65_counterexample_real : ¬ rubi734r65.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r65.conditions rubi734r65.body rubi734r65.result rubi734r65.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi734r65, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r65.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r65, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r65, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r67_counterexample_real : ¬ rubi734r67.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r67.conditions rubi734r67.body rubi734r67.result rubi734r67.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi734r67, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r67.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -2 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r67, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r67, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r71_counterexample_real : ¬ rubi734r71.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r71.conditions rubi734r71.body rubi734r71.result rubi734r71.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi734r71, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r71, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r71.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r71, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r71, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r75_counterexample_real : ¬ rubi734r75.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r75.conditions rubi734r75.body rubi734r75.result rubi734r75.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" ∨ s = "b" ∨ s = "f" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi734r75, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r75, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi734r75.integrals[0]!, by simp [rubi734r75], ?_⟩
  intro h
  simp [rubi734r75, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi734r81_counterexample_real : ¬ rubi734r81.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r81.conditions rubi734r81.body rubi734r81.result rubi734r81.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi734r81, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r81.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r81, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r81, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r9_counterexample_real : ¬ rubi734r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r9.conditions rubi734r9.body rubi734r9.result rubi734r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi734r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r93_counterexample_real : ¬ rubi734r93.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r93.conditions rubi734r93.body rubi734r93.result rubi734r93.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi734r93, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r93, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r93.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r93, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi734r97_counterexample_real : ¬ rubi734r97.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi734r97.conditions rubi734r97.body rubi734r97.result rubi734r97.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi734r97, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi734r97, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi734r97.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else if s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi734r97, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi734r97, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi735r7_counterexample_real : ¬ rubi735r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi735r7.conditions rubi735r7.body rubi735r7.result rubi735r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "e" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi735r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi735r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi735r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "e" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi735r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi735r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi737r15_counterexample_real : ¬ rubi737r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi737r15.conditions rubi737r15.body rubi737r15.result rubi737r15.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then 1 else 0) (-1 : ℝ) (by simp [rubi737r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (-1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi737r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi737r15.integrals[0]!, by simp [rubi737r15], ?_⟩
  intro h
  simp [rubi737r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

end OSR.IntegrationRec126
