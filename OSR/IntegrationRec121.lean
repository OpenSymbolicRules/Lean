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

namespace OSR.IntegrationRec121

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.1.2 #9 -/
def rubi512r9 : CRule where
  id := "integration.rubi_5_1_2_r9"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "x") (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.int (-2)) (.var "n")]
  priority := 9601
  description := "RUBI 5.1.2 #9"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n:9" "5 Inverse trig functions/5.1 Inverse sine/5.1.2 (d x)^m (a+b arcsin(c x))^n.m#9"

/-- RUBI 5.1.5 #15 -/
def rubi515r15 : CRule where
  id := "integration.rubi_5_1_5_r15"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "g")) (.app2 .add (.var "m") (.int 2))) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9602
  description := "RUBI 5.1.5 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:15" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#15"

/-- RUBI 5.1.5 #16 -/
def rubi515r16 : CRule where
  id := "integration.rubi_5_1_5_r16"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m"))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.var "g")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.var "f")) (.var "x"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.var "g")) (.app2 .add (.var "m") (.int 2))) (.pow (.var "x") (.int 2)))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.int 0) (.var "m"),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9603
  description := "RUBI 5.1.5 #16"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:16" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#16"

/-- RUBI 5.1.5 #21 -/
def rubi515r21 : CRule where
  id := "integration.rubi_5_1_5_r21"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "d") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 9604
  description := "RUBI 5.1.5 #21"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:21" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#21"

/-- RUBI 5.1.5 #22 -/
def rubi515r22 : CRule where
  id := "integration.rubi_5_1_5_r22"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0),
    .gt (.var "d") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 9605
  description := "RUBI 5.1.5 #22"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:22" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#22"

/-- RUBI 5.1.5 #29 -/
def rubi515r29 : CRule where
  id := "integration.rubi_5_1_5_r29"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9606
  description := "RUBI 5.1.5 #29"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:29" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#29"

/-- RUBI 5.1.5 #3 -/
def rubi515r3 : CRule where
  id := "integration.rubi_5_1_5_r3"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9607
  description := "RUBI 5.1.5 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:3" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#3"

/-- RUBI 5.1.5 #30 -/
def rubi515r30 : CRule where
  id := "integration.rubi_5_1_5_r30"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m")))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .ln (.app2 .mul (.var "h") (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.var "m"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "h", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "d") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9608
  description := "RUBI 5.1.5 #30"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:30" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#30"

/-- RUBI 5.1.5 #4 -/
def rubi515r4 : CRule where
  id := "integration.rubi_5_1_5_r4"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 9609
  description := "RUBI 5.1.5 #4"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n:4" "5 Inverse trig functions/5.1 Inverse sine/5.1.5 u (a+b arcsin(c x))^n.m#4"

/-- RUBI 5.1.6 #12 -/
def rubi516r12 : CRule where
  id := "integration.rubi_5_1_6_r12"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:12"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "n")) (.app2 .root (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "c")) (.var "d")) (.pow (.var "x") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.var "x")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.pow (.var "b") (.int 2))) (.var "n")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.var "n") (.int 1)]
  priority := 9610
  description := "RUBI 5.1.6 #12"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:12" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#12"

/-- RUBI 5.1.6 #13 -/
def rubi516r13 : CRule where
  id := "integration.rubi_5_1_6_r13"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:13"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.var "n")) (.app2 .root (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "c")) (.var "d")) (.pow (.var "x") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.var "x")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.pow (.var "b") (.int 2))) (.var "n")) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.var "n") (.int 1)]
  priority := 9611
  description := "RUBI 5.1.6 #13"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:13" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#13"

/-- RUBI 5.1.6 #26 -/
def rubi516r26 : CRule where
  id := "integration.rubi_5_1_6_r26"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:26"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "c")) (.var "d")) (.pow (.var "x") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.var "x") (.int 4)))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.var "x")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.int (-2))]
  priority := 9612
  description := "RUBI 5.1.6 #26"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:26" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#26"

/-- RUBI 5.1.6 #27 -/
def rubi516r27 : CRule where
  id := "integration.rubi_5_1_6_r27"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:27"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.var "n"))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "c")) (.var "d")) (.pow (.var "x") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.var "x") (.int 4)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.var "x")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.pow (.var "b") (.int 2))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2))))))) (.app2 .add (.var "n") (.int 2))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.pow (.var "c") (.int 2)) (.int 1),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.int (-2))]
  priority := 9613
  description := "RUBI 5.1.6 #27"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:27" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#27"

/-- RUBI 5.1.6 #36 -/
def rubi516r36 : CRule where
  id := "integration.rubi_5_1_6_r36"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:36"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arcsin (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.int 2))) (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arcsin (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.int 2))) (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.app2 .root (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2))) (.pow (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.int 2))) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))))) (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.int 1)]
  priority := 9614
  description := "RUBI 5.1.6 #36"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:36" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#36"

/-- RUBI 5.1.6 #37 -/
def rubi516r37 : CRule where
  id := "integration.rubi_5_1_6_r37"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:37"
  shape := .antiderivRec; x := "x"
  body := (.app1 .arccos (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.int 2))) (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.var "x") (.app1 .arccos (.app2 .add (.app2 .mul (.var "a") (.pow (.var "x") (.int 2))) (.app2 .mul (.var "b") (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.app2 .root (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2))) (.pow (.app2 .root (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.int 2))) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))))) (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.app2 .add (.app2 .mul (.var "b") (.var "d")) (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .root (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.int 2)))) (.int 2)))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .mul (.pow (.var "b") (.int 2)) (.var "c")) (.int 1)]
  priority := 9615
  description := "RUBI 5.1.6 #37"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine:37" "5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m#37"

/-- RUBI 5.3.2 #15 -/
def rubi532r15 : CRule where
  id := "integration.rubi_5_3_2_r15"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.2 (d x)^m (a+b arctan(c x^n))^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.pow (.var "d") (.var "n")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.var "x")) (.app2 .add (.var "m") (.var "n"))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.int (.var "n"),
    .ne (.var "m") (.int (-1))]
  priority := 9616
  description := "RUBI 5.3.2 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.2 (d x)^m (a+b arctan(c x^n))^p:15" "5 Inverse trig functions/5.3 Inverse tangent/5.3.2 (d x)^m (a+b arctan(c x^n))^p.m#15"

/-- RUBI 5.3.3 #1 -/
def rubi533r1 : CRule where
  id := "integration.rubi_5_3_3_r1"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1)))))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "p")) (.pow (.var "e") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .ln (.app2 .mul (.int 2) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1)))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "e") (.int 2))) (.int 0)]
  priority := 9617
  description := "RUBI 5.3.3 #1"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:1" "5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p.m#1"

/-- RUBI 5.3.3 #13 -/
def rubi533r13 : CRule where
  id := "integration.rubi_5_3_3_r13"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app1 .ln (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.var "e") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.var "e") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .ln (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.int (.var "n")]
  priority := 9618
  description := "RUBI 5.3.3 #13"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:13" "5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p.m#13"

/-- RUBI 5.3.3 #15 -/
def rubi533r15 : CRule where
  id := "integration.rubi_5_3_3_r15"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.var "x") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.app2 .mul (.int 2) (.var "n"))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.var "m") (.int (-1))]
  priority := 9619
  description := "RUBI 5.3.3 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:15" "5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p.m#15"

/-- RUBI 5.3.3 #9 -/
def rubi533r9 : CRule where
  id := "integration.rubi_5_3_3_r9"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.ne (.var "q") (.int (-1))]
  priority := 9620
  description := "RUBI 5.3.3 #9"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p:9" "5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p.m#9"

/-- RUBI 5.3.4 #1 -/
def rubi534r1 : CRule where
  id := "integration.rubi_5_3_4_r1"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "f") (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "f")) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "e") (.int 2))) (.int 0),
    .gt (.var "m") (.int 0)]
  priority := 9621
  description := "RUBI 5.3.4 #1"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:1" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#1"

/-- RUBI 5.3.4 #103 -/
def rubi534r103 : CRule where
  id := "integration.rubi_5_3_4_r103"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:103"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.ne (.var "q") (.int (-1))]
  priority := 9622
  description := "RUBI 5.3.4 #103"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:103" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#103"

/-- RUBI 5.3.4 #11 -/
def rubi534r11 : CRule where
  id := "integration.rubi_5_3_4_r11"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.var "q")) (.pow (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "q")) (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "q") (.int 0),
    .gt (.var "p") (.int 1)]
  priority := 9623
  description := "RUBI 5.3.4 #11"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:11" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#11"

/-- RUBI 5.3.4 #115 -/
def rubi534r115 : CRule where
  id := "integration.rubi_5_3_4_r115"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:115"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.app1 .ln (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "g")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.var "x"))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "f") (.int 2))) (.pow (.var "g") (.int 2))) (.int 0)]
  priority := 9624
  description := "RUBI 5.3.4 #115"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:115" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#115"

/-- RUBI 5.3.4 #15 -/
def rubi534r15 : CRule where
  id := "integration.rubi_5_3_4_r15"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:15"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .ne (.var "p") (.int (-1))]
  priority := 9625
  description := "RUBI 5.3.4 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:15" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#15"

/-- RUBI 5.3.4 #23 -/
def rubi534r23 : CRule where
  id := "integration.rubi_5_3_4_r23"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.pow (.var "d") (.int 2))) (.app2 .add (.var "p") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.int 2) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0)]
  priority := 9626
  description := "RUBI 5.3.4 #23"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:23" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#23"

/-- RUBI 5.3.4 #27 -/
def rubi534r27 : CRule where
  id := "integration.rubi_5_3_4_r27"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "c")) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x")))))))]
  independent := ["a", "b", "c", "d", "e", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "q"),
    .ne (.var "q") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 9627
  description := "RUBI 5.3.4 #27"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:27" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#27"

/-- RUBI 5.3.4 #3 -/
def rubi534r3 : CRule where
  id := "integration.rubi_5_3_4_r3"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "x") (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")) (.app1 .ln (.app2 .add (.int 2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1))))))) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "p")) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .ln (.app2 .add (.int 2) (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.var "d") (.int (-1))))) (.int (-1))))))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 0),
    .eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "e") (.int 2))) (.int 0)]
  priority := 9628
  description := "RUBI 5.3.4 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:3" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#3"

/-- RUBI 5.3.4 #31 -/
def rubi534r31 : CRule where
  id := "integration.rubi_5_3_4_r31"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "p")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 4) (.var "c")) (.var "d")) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "x")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.var "q")) (.int 3)) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 4) (.pow (.app2 .add (.var "q") (.int 1)) (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "q"),
    .gt (.var "p") (.int 1),
    .ne (.var "q") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 9629
  description := "RUBI 5.3.4 #31"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:31" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#31"

/-- RUBI 5.3.4 #33 -/
def rubi534r33 : CRule where
  id := "integration.rubi_5_3_4_r33"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "q"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "q"),
    .gt (.int (-1)) (.var "p")]
  priority := 9630
  description := "RUBI 5.3.4 #33"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:33" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#33"

/-- RUBI 5.3.4 #45 -/
def rubi534r45 : CRule where
  id := "integration.rubi_5_3_4_r45"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:45"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "e") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "f") (.int 2))) (.pow (.var "e") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 9631
  description := "RUBI 5.3.4 #45"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:45" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#45"

/-- RUBI 5.3.4 #47 -/
def rubi534r47 : CRule where
  id := "integration.rubi_5_3_4_r47"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:47"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .mul (.var "d") (.pow (.var "f") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.gt (.var "p") (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 9632
  description := "RUBI 5.3.4 #47"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:47" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#47"

/-- RUBI 5.3.4 #55 -/
def rubi534r55 : CRule where
  id := "integration.rubi_5_3_4_r55"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:55"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "p")]
  priority := 9633
  description := "RUBI 5.3.4 #55"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:55" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#55"

/-- RUBI 5.3.4 #59 -/
def rubi534r59 : CRule where
  id := "integration.rubi_5_3_4_r59"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:59"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "q") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "p")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "q") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "q")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "q", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "p") (.int 0),
    .ne (.var "q") (.int (-1))]
  priority := 9634
  description := "RUBI 5.3.4 #59"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:59" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#59"

/-- RUBI 5.3.4 #61 -/
def rubi534r61 : CRule where
  id := "integration.rubi_5_3_4_r61"; legacyId := some "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:61"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.var "p"))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2))))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "p") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arctan (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "p") (.int 2)))) (.pow (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "p"),
    .ne (.var "p") (.int (-2))]
  priority := 9635
  description := "RUBI 5.3.4 #61"
  provenance := migrated "rubi:5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p:61" "5 Inverse trig functions/5.3 Inverse tangent/5.3.4 u (a+b arctan(c x))^p.m#61"

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


theorem rubi512r9_counterexample_real : ¬ rubi512r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi512r9.conditions rubi512r9.body rubi512r9.result rubi512r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi512r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi512r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi512r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi512r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi512r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r15_counterexample_real : ¬ rubi515r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r15.conditions rubi515r15.body rubi515r15.result rubi515r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r16_counterexample_real : ¬ rubi515r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r16.conditions rubi515r16.body rubi515r16.result rubi515r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r21_counterexample_real : ¬ rubi515r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r21.conditions rubi515r21.body rubi515r21.result rubi515r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi515r21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r22_counterexample_real : ¬ rubi515r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r22.conditions rubi515r22.body rubi515r22.result rubi515r22.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi515r22, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "g" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r22, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r29_counterexample_real : ¬ rubi515r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r29.conditions rubi515r29.body rubi515r29.result rubi515r29.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r29, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r29, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r3_counterexample_real : ¬ rubi515r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r3.conditions rubi515r3.body rubi515r3.result rubi515r3.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r30_counterexample_real : ¬ rubi515r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r30.conditions rubi515r30.body rubi515r30.result rubi515r30.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r30, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "h" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r30, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi515r4_counterexample_real : ¬ rubi515r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi515r4.conditions rubi515r4.body rubi515r4.result rubi515r4.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi515r4, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi515r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi515r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi515r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi515r4, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi516r12_counterexample_real : ¬ rubi516r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r12.conditions rubi516r12.body rubi516r12.result rubi516r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi516r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi516r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi516r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi516r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi516r13_counterexample_real : ¬ rubi516r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r13.conditions rubi516r13.body rubi516r13.result rubi516r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi516r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi516r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi516r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi516r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi516r26_counterexample_real : ¬ rubi516r26.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r26.conditions rubi516r26.body rubi516r26.result rubi516r26.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then -3 else if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi516r26, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi516r26.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then -3 else if s = "b" ∨ s = "c" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi516r26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi516r26, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi516r27_counterexample_real : ¬ rubi516r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r27.conditions rubi516r27.body rubi516r27.result rubi516r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" then -1 else if s = "n" then -3 else 0) (1 : ℝ) (by simp [rubi516r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi516r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" then -1 else if s = "n" then -3 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi516r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi516r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi516r36_counterexample_real : ¬ rubi516r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r36.conditions rubi516r36.body rubi516r36.result rubi516r36.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi516r36, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi516r36.integrals[0]!, by simp [rubi516r36], ?_⟩
  intro h
  simp [rubi516r36, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi516r37_counterexample_real : ¬ rubi516r37.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi516r37.conditions rubi516r37.body rubi516r37.result rubi516r37.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "c" then 1 else 0) (1 : ℝ) (by simp [rubi516r37, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi516r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi516r37.integrals[0]!, by simp [rubi516r37], ?_⟩
  intro h
  simp [rubi516r37, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi532r15_counterexample_real : ¬ rubi532r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi532r15.conditions rubi532r15.body rubi532r15.result rubi532r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi532r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi532r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi532r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi532r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi532r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi533r1_counterexample_real : ¬ rubi533r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi533r1.conditions rubi533r1.body rubi533r1.result rubi533r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi533r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi533r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi533r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi533r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi533r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi533r13_counterexample_real : ¬ rubi533r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi533r13.conditions rubi533r13.body rubi533r13.result rubi533r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi533r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi533r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi533r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi533r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi533r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi533r15_counterexample_real : ¬ rubi533r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi533r15.conditions rubi533r15.body rubi533r15.result rubi533r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi533r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi533r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi533r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi533r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi533r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi533r9_counterexample_real : ¬ rubi533r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi533r9.conditions rubi533r9.body rubi533r9.result rubi533r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi533r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi533r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi533r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi533r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi533r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r1_counterexample_real : ¬ rubi534r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r1.conditions rubi534r1.body rubi534r1.result rubi534r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "m" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r103_counterexample_real : ¬ rubi534r103.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r103.conditions rubi534r103.body rubi534r103.result rubi534r103.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi534r103, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r103.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r103, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r103, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r11_counterexample_real : ¬ rubi534r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r11.conditions rubi534r11.body rubi534r11.result rubi534r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi534r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "q" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r115_counterexample_real : ¬ rubi534r115.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r115.conditions rubi534r115.body rubi534r115.result rubi534r115.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r115, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r115, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r115.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "b" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r115, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r115, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r15_counterexample_real : ¬ rubi534r15.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi534r15.conditions rubi534r15.body rubi534r15.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi534r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi534r23_counterexample_real : ¬ rubi534r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r23.conditions rubi534r23.body rubi534r23.result rubi534r23.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r23, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r23, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r27_counterexample_real : ¬ rubi534r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r27.conditions rubi534r27.body rubi534r27.result rubi534r27.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi534r27, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r27, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r3_counterexample_real : ¬ rubi534r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r3.conditions rubi534r3.body rubi534r3.result rubi534r3.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" ∨ s = "d" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r3, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi534r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi534r3.integrals[0]!, by simp [rubi534r3], ?_⟩
  intro h
  simp [rubi534r3, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi534r31_counterexample_real : ¬ rubi534r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r31.conditions rubi534r31.body rubi534r31.result rubi534r31.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi534r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "q" then -3 else if s = "b" ∨ s = "d" ∨ s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r33_counterexample_real : ¬ rubi534r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r33.conditions rubi534r33.body rubi534r33.result rubi534r33.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else 0) (1 : ℝ) (by simp [rubi534r33, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "d" ∨ s = "p" ∨ s = "q" then -2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r33, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r45_counterexample_real : ¬ rubi534r45.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r45.conditions rubi534r45.body rubi534r45.result rubi534r45.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi534r45, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r45.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "d" ∨ s = "f" ∨ s = "p" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r45, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r45, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r47_counterexample_real : ¬ rubi534r47.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r47.conditions rubi534r47.body rubi534r47.result rubi534r47.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi534r47, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (by filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with w hw; simp [rubi534r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, hw] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r47.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r47, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r47, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r55_counterexample_real : ¬ rubi534r55.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r55.conditions rubi534r55.body rubi534r55.result rubi534r55.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi534r55, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r55.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" ∨ s = "f" ∨ s = "m" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r55, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r59_counterexample_real : ¬ rubi534r59.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r59.conditions rubi534r59.body rubi534r59.result rubi534r59.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "d" ∨ s = "p" ∨ s = "q" then 1 else 0) (1 : ℝ) (by simp [rubi534r59, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r59.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "d" ∨ s = "p" ∨ s = "q" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r59, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi534r61_counterexample_real : ¬ rubi534r61.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi534r61.conditions rubi534r61.body rubi534r61.result rubi534r61.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi534r61, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi534r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi534r61.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then -3 else if s = "a" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi534r61, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi534r61, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec121
