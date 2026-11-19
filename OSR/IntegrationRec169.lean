import OSR.IntegrationRec91

/-!
# Integration (RUBI): sinh and cosh split into exponentials

`sinh u = (exp u - exp(-u))/2` and `cosh u = (exp u + exp(-u))/2` (RUBI writes
`exp u` as `E^u`).  6.1.12 #1, #2, #7, #8, #29, #30, #55, #56, 6.1.13 #1, #2
and 6.7.9 #91 to #94 are proved over ℝ and ℂ.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec169

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.1.12 #1 -/
def rubi6112r1 : CRule where
  id := "integration.rubi_6_1_12_r1"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n"))))))]
  independent := ["c", "d", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1)]
  priority := 12040
  description := "RUBI 6.1.12 #1"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:1" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#1"

/-- RUBI 6.1.12 #2 -/
def rubi6112r2 : CRule where
  id := "integration.rubi_6_1_12_r2"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n"))))))]
  independent := ["c", "d", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1)]
  priority := 12041
  description := "RUBI 6.1.12 #2"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:2" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#2"

/-- RUBI 6.1.12 #29 -/
def rubi6112r29 : CRule where
  id := "integration.rubi_6_1_12_r29"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 12042
  description := "RUBI 6.1.12 #29"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:29" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#29"

/-- RUBI 6.1.12 #30 -/
def rubi6112r30 : CRule where
  id := "integration.rubi_6_1_12_r30"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 12043
  description := "RUBI 6.1.12 #30"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:30" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#30"

/-- RUBI 6.1.12 #55 -/
def rubi6112r55 : CRule where
  id := "integration.rubi_6_1_12_r55"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:55"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  priority := 12044
  description := "RUBI 6.1.12 #55"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:55" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#55"

/-- RUBI 6.1.12 #56 -/
def rubi6112r56 : CRule where
  id := "integration.rubi_6_1_12_r56"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:56"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "e", "m", "n"]
  priority := 12045
  description := "RUBI 6.1.12 #56"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:56" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#56"

/-- RUBI 6.1.12 #7 -/
def rubi6112r7 : CRule where
  id := "integration.rubi_6_1_12_r7"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n"))))))]
  independent := ["c", "d", "n"]
  priority := 12046
  description := "RUBI 6.1.12 #7"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:7" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#7"

/-- RUBI 6.1.12 #8 -/
def rubi6112r8 : CRule where
  id := "integration.rubi_6_1_12_r8"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .mul (.int (-1)) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.var "x") (.var "n"))))))]
  independent := ["c", "d", "n"]
  priority := 12047
  description := "RUBI 6.1.12 #8"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p:8" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m#8"

/-- RUBI 6.1.13 #1 -/
def rubi6113r1 : CRule where
  id := "integration.rubi_6_1_13_r1"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:1"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .add (.app2 .mul (.int (-1)) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c"]
  priority := 12048
  description := "RUBI 6.1.13 #1"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:1" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#1"

/-- RUBI 6.1.13 #2 -/
def rubi6113r2 : CRule where
  id := "integration.rubi_6_1_13_r2"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))),
    ("I2", (.app1 .exp (.app2 .add (.app2 .add (.app2 .mul (.int (-1)) (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "x"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c"]
  priority := 12049
  description := "RUBI 6.1.13 #2"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:2" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#2"

/-- RUBI 6.7.9 #91 -/
def rubi679r91 : CRule where
  id := "integration.rubi_6_7_9_r91"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:91"
  shape := .antiderivRec; x := "x"
  body := (.app1 .sinh (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))),
    ("I2", (.app1 .exp (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n"]
  priority := 12050
  description := "RUBI 6.7.9 #91"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:91" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#91"

/-- RUBI 6.7.9 #92 -/
def rubi679r92 : CRule where
  id := "integration.rubi_6_7_9_r92"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:92"
  shape := .antiderivRec; x := "x"
  body := (.app1 .cosh (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .exp (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))),
    ("I2", (.app1 .exp (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))]
  independent := ["a", "b", "c", "d", "n"]
  priority := 12051
  description := "RUBI 6.7.9 #92"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:92" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#92"

/-- RUBI 6.7.9 #93 -/
def rubi679r93 : CRule where
  id := "integration.rubi_6_7_9_r93"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:93"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  priority := 12052
  description := "RUBI 6.7.9 #93"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:93" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#93"

/-- RUBI 6.7.9 #94 -/
def rubi679r94 : CRule where
  id := "integration.rubi_6_7_9_r94"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:94"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2)))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .exp (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  priority := 12053
  description := "RUBI 6.7.9 #94"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:94" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#94"

/-! ## Proofs -/

theorem rubi6112r1_real : rubi6112r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r1.conditions rubi6112r1.body rubi6112r1.result rubi6112r1.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r1, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r1, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r1, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r1_complex : rubi6112r1.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r1.conditions rubi6112r1.body rubi6112r1.result rubi6112r1.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r1, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r1, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r1, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r2_real : rubi6112r2.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r2.conditions rubi6112r2.body rubi6112r2.result rubi6112r2.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r2, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r2, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r2, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r2_complex : rubi6112r2.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r2.conditions rubi6112r2.body rubi6112r2.result rubi6112r2.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r2, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r2, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r2, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r29_real : rubi6112r29.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r29.conditions rubi6112r29.body rubi6112r29.result rubi6112r29.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r29, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r29, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r29, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r29, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r29_complex : rubi6112r29.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r29.conditions rubi6112r29.body rubi6112r29.result rubi6112r29.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r29, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r29, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r29, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r29, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r30_real : rubi6112r30.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r30.conditions rubi6112r30.body rubi6112r30.result rubi6112r30.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r30, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r30, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r30, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r30, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r30_complex : rubi6112r30.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r30.conditions rubi6112r30.body rubi6112r30.result rubi6112r30.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r30, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r30, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r30, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r30, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r55_real : rubi6112r55.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r55.conditions rubi6112r55.body rubi6112r55.result rubi6112r55.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r55, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r55, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r55, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r55, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r55_complex : rubi6112r55.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r55.conditions rubi6112r55.body rubi6112r55.result rubi6112r55.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r55, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r55, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r55, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r55, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r55, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r56_real : rubi6112r56.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r56.conditions rubi6112r56.body rubi6112r56.result rubi6112r56.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r56, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r56, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r56, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r56, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r56, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r56_complex : rubi6112r56.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r56.conditions rubi6112r56.body rubi6112r56.result rubi6112r56.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r56, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r56, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r56, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r56, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r56, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r7_real : rubi6112r7.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r7.conditions rubi6112r7.body rubi6112r7.result rubi6112r7.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r7, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r7, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r7, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r7_complex : rubi6112r7.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r7.conditions rubi6112r7.body rubi6112r7.result rubi6112r7.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r7, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r7, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r7, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r7, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r8_real : rubi6112r8.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6112r8.conditions rubi6112r8.body rubi6112r8.result rubi6112r8.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r8, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r8, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6112r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r8, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6112r8_complex : rubi6112r8.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6112r8.conditions rubi6112r8.body rubi6112r8.result rubi6112r8.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6112r8, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6112r8, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6112r8, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6112r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6112r8, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6113r1_real : rubi6113r1.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r1.conditions rubi6113r1.body rubi6113r1.result rubi6113r1.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6113r1, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6113r1, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6113r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6113r1, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6113r1_complex : rubi6113r1.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r1.conditions rubi6113r1.body rubi6113r1.result rubi6113r1.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6113r1, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6113r1, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6113r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6113r1, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi6113r2_real : rubi6113r2.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi6113r2.conditions rubi6113r2.body rubi6113r2.result rubi6113r2.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6113r2, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6113r2, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi6113r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6113r2, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi6113r2_complex : rubi6113r2.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi6113r2.conditions rubi6113r2.body rubi6113r2.result rubi6113r2.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi6113r2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi6113r2, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi6113r2, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi6113r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi6113r2, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r91_real : rubi679r91.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r91.conditions rubi679r91.body rubi679r91.result rubi679r91.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r91, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r91, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r91, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi679r91, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r91, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r91_complex : rubi679r91.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r91.conditions rubi679r91.body rubi679r91.result rubi679r91.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r91, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r91, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r91, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi679r91, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r91, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r92_real : rubi679r92.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r92.conditions rubi679r92.body rubi679r92.result rubi679r92.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r92, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r92, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r92, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi679r92, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r92, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r92_complex : rubi679r92.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r92.conditions rubi679r92.body rubi679r92.result rubi679r92.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r92, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r92, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r92, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi679r92, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r92, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r93_real : rubi679r93.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r93.conditions rubi679r93.body rubi679r93.result rubi679r93.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r93, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r93, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r93, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi679r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r93, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r93_complex : rubi679r93.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r93.conditions rubi679r93.body rubi679r93.result rubi679r93.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r93, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r93, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r93, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi679r93, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r93, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r94_real : rubi679r94.Holds .real := by
  show AntiderivRecHolds Interp.real "x" rubi679r94.conditions rubi679r94.body rubi679r94.result rubi679r94.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r94, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r94, Defined, eval, Interp.real, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r94, Defined, eval, recEnv, Interp.real, i2, im1]
  · simp only [rubi679r94, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r94, eval, recEnv, Interp.real, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Real.sinh_eq, Real.cosh_eq]
    first | ring_nf | (trace_state; sorry)

theorem rubi679r94_complex : rubi679r94.Holds .complex := by
  show AntiderivRecHolds Interp.complex "x" rubi679r94.conditions rubi679r94.body rubi679r94.result rubi679r94.integrals
  intro env hc t hF
  have im1 : intValue? (-1 : ℂ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have i2 : intValue? (2 : ℂ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  refine ⟨fun i hi => ?_, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · simp only [rubi679r94, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> filter_upwards [hF] with w hw <;>
    simp [rubi679r94, Defined, eval, Interp.complex, i2, im1] at hw ⊢ <;> first | tauto | (trace_state; sorry)
  · exact Eventually.of_forall fun w => by simp [rubi679r94, Defined, eval, recEnv, Interp.complex, i2, im1]
  · simp only [rubi679r94, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hΦ
    obtain ⟨hΦ1, hΦ2⟩ := hΦ
    simp [rubi679r94, eval, recEnv, Interp.complex, i2, im1] at hΦ1 hΦ2 ⊢
    refine HasDerivAt.congr_deriv (by
      first
        | exact (hΦ1.const_mul _).add ((hΦ2.const_mul _).neg)
        | exact (hΦ1.const_mul _).add (hΦ2.const_mul _)
        | exact ((hΦ1.const_mul _).neg).add (hΦ2.const_mul _)) ?_
    simp only [Complex.sinh, Complex.cosh]
    first | ring_nf | (trace_state; sorry)

end OSR.IntegrationRec169
