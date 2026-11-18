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

namespace OSR.IntegrationRec123

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 6.1.13 #11 -/
def rubi6113r11 : CRule where
  id := "integration.rubi_6_1_13_r11"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.var "m") (.int 1),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9801
  description := "RUBI 6.1.13 #11"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:11" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#11"

/-- RUBI 6.1.13 #12 -/
def rubi6113r12 : CRule where
  id := "integration.rubi_6_1_13_r12"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.var "m") (.int 1),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9802
  description := "RUBI 6.1.13 #12"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:12" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#12"

/-- RUBI 6.1.13 #13 -/
def rubi6113r13 : CRule where
  id := "integration.rubi_6_1_13_r13"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9803
  description := "RUBI 6.1.13 #13"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:13" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#13"

/-- RUBI 6.1.13 #14 -/
def rubi6113r14 : CRule where
  id := "integration.rubi_6_1_13_r14"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "e") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "e") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9804
  description := "RUBI 6.1.13 #14"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:14" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#14"

/-- RUBI 6.1.13 #15 -/
def rubi6113r15 : CRule where
  id := "integration.rubi_6_1_13_r15"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9805
  description := "RUBI 6.1.13 #15"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:15" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#15"

/-- RUBI 6.1.13 #16 -/
def rubi6113r16 : CRule where
  id := "integration.rubi_6_1_13_r16"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9806
  description := "RUBI 6.1.13 #16"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:16" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#16"

/-- RUBI 6.1.13 #17 -/
def rubi6113r17 : CRule where
  id := "integration.rubi_6_1_13_r17"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9807
  description := "RUBI 6.1.13 #17"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:17" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#17"

/-- RUBI 6.1.13 #18 -/
def rubi6113r18 : CRule where
  id := "integration.rubi_6_1_13_r18"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.pow (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 1))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app2 .add (.var "m") (.int 2))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))))]
  independent := ["a", "b", "c", "d", "e", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9808
  description := "RUBI 6.1.13 #18"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:18" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#18"

/-- RUBI 6.1.13 #7 -/
def rubi6113r7 : CRule where
  id := "integration.rubi_6_1_13_r7"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:7"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9809
  description := "RUBI 6.1.13 #7"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:7" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#7"

/-- RUBI 6.1.13 #8 -/
def rubi6113r8 : CRule where
  id := "integration.rubi_6_1_13_r8"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:8"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .mul (.app2 .mul (.var "e") (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9810
  description := "RUBI 6.1.13 #8"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:8" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#8"

/-- RUBI 6.1.13 #9 -/
def rubi6113r9 : CRule where
  id := "integration.rubi_6_1_13_r9"; legacyId := some "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))) (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "e") (.app1 .cosh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2)))))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d")))) (.pow (.app2 .mul (.int 2) (.var "c")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app1 .sinh (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))) (.app2 .mul (.var "c") (.pow (.var "x") (.int 2))))))]
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "e")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "c")) (.var "d"))) (.int 0)]
  priority := 9811
  description := "RUBI 6.1.13 #9"
  provenance := migrated "rubi:6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n:9" "6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.13 (d+e x)^m sinh(a+b x+c x^2)^n.m#9"

/-- RUBI 6.3.11 #11 -/
def rubi6311r11 : CRule where
  id := "integration.rubi_6_3_11_r11"; legacyId := some "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.int 2)))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.var "x") (.var "m"))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "m", "n"]
  priority := 9812
  description := "RUBI 6.3.11 #11"
  provenance := migrated "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p:11" "6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p.m#11"

/-- RUBI 6.3.11 #12 -/
def rubi6311r12 : CRule where
  id := "integration.rubi_6_3_11_r12"; legacyId := some "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.var "x") (.var "m")) (.pow (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n"))))) (.int 2)))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "x") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)))) (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.int 1)) (.pow (.app2 .mul (.var "d") (.var "n")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.var "x") (.var "m"))),
    ("I2", (.app2 .mul (.pow (.var "x") (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n")))) (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.pow (.var "x") (.var "n")))))))]
  independent := ["c", "d", "m", "n"]
  priority := 9813
  description := "RUBI 6.3.11 #12"
  provenance := migrated "rubi:6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p:12" "6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p.m#12"

/-- RUBI 6.7.6 #1 -/
def rubi676r1 : CRule where
  id := "integration.rubi_6_7_6_r1"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9814
  description := "RUBI 6.7.6 #1"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:1" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#1"

/-- RUBI 6.7.6 #16 -/
def rubi676r16 : CRule where
  id := "integration.rubi_6_7_6_r16"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9815
  description := "RUBI 6.7.6 #16"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:16" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#16"

/-- RUBI 6.7.6 #17 -/
def rubi676r17 : CRule where
  id := "integration.rubi_6_7_6_r17"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9816
  description := "RUBI 6.7.6 #17"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:17" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#17"

/-- RUBI 6.7.6 #18 -/
def rubi676r18 : CRule where
  id := "integration.rubi_6_7_6_r18"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9817
  description := "RUBI 6.7.6 #18"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:18" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#18"

/-- RUBI 6.7.6 #19 -/
def rubi676r19 : CRule where
  id := "integration.rubi_6_7_6_r19"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9818
  description := "RUBI 6.7.6 #19"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:19" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#19"

/-- RUBI 6.7.6 #2 -/
def rubi676r2 : CRule where
  id := "integration.rubi_6_7_6_r2"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.app1 .sinh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .cosh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9819
  description := "RUBI 6.7.6 #2"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:2" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#2"

/-- RUBI 6.7.6 #20 -/
def rubi676r20 : CRule where
  id := "integration.rubi_6_7_6_r20"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9820
  description := "RUBI 6.7.6 #20"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:20" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#20"

/-- RUBI 6.7.6 #21 -/
def rubi676r21 : CRule where
  id := "integration.rubi_6_7_6_r21"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app1 .coth (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .csch (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9821
  description := "RUBI 6.7.6 #21"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:21" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#21"

/-- RUBI 6.7.6 #6 -/
def rubi676r6 : CRule where
  id := "integration.rubi_6_7_6_r6"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "n", "m", "p"]
  conditions := [.eq (.var "p") (.int 1),
    .gt (.var "m") (.int 0)]
  priority := 9822
  description := "RUBI 6.7.6 #6"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:6" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#6"

/-- RUBI 6.7.6 #7 -/
def rubi676r7 : CRule where
  id := "integration.rubi_6_7_6_r7"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .mul (.var "b") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "n", "m", "p"]
  conditions := [.eq (.var "p") (.int 1),
    .gt (.var "m") (.int 0)]
  priority := 9823
  description := "RUBI 6.7.6 #7"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:7" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#7"

/-- RUBI 6.7.6 #8 -/
def rubi676r8 : CRule where
  id := "integration.rubi_6_7_6_r8"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .sech (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 2))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .tanh (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9824
  description := "RUBI 6.7.6 #8"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:8" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#8"

/-- RUBI 6.7.6 #9 -/
def rubi676r9 : CRule where
  id := "integration.rubi_6_7_6_r9"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:9"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app1 .csch (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.int 2))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "m")) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .coth (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n", "m"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 9825
  description := "RUBI 6.7.6 #9"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p:9" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.6 (c+d x)^m hyper(a+b x)^n hyper(a+b x)^p.m#9"

/-- RUBI 6.7.7 #31 -/
def rubi677r31 : CRule where
  id := "integration.rubi_6_7_7_r31"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "m"))) (.pow (.app2 .add (.var "f") (.app2 .mul (.var "g") (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.pow (.var "g") (.var "n")) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .coth (.app2 .add (.app2 .mul (.var "d") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "e") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.var "m"))))]
  independent := ["F", "a", "b", "c", "d", "e", "f", "g", "m", "n"]
  conditions := [.eq (.app2 .add (.var "f") (.var "g")) (.int 0),
    .int (.var "m"),
    .int (.var "n"),
    .eq (.app2 .add (.var "m") (.var "n")) (.int 0)]
  priority := 9826
  description := "RUBI 6.7.7 #31"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:31" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#31"

/-- RUBI 6.7.7 #5 -/
def rubi677r5 : CRule where
  id := "integration.rubi_6_7_7_r5"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.var "n") (.int (-2))]
  priority := 9827
  description := "RUBI 6.7.7 #5"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:5" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#5"

/-- RUBI 6.7.7 #6 -/
def rubi677r6 : CRule where
  id := "integration.rubi_6_7_7_r6"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:6"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app1 .ln (.var "F"))) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 2)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "e") (.int 2)) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "F") (.app2 .mul (.var "c") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))))) (.app1 .sinh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.pow (.app1 .cosh (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.int (-1)))))
  independent := ["F", "a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "e") (.int 2)) (.pow (.app2 .add (.var "n") (.int 2)) (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "c") (.int 2))) (.pow (.app1 .ln (.var "F")) (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-1)),
    .ne (.var "n") (.int (-2))]
  priority := 9828
  description := "RUBI 6.7.7 #6"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n:6" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m#6"

/-- RUBI 6.7.8 #13 -/
def rubi678r13 : CRule where
  id := "integration.rubi_6_7_8_r13"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:13"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9829
  description := "RUBI 6.7.8 #13"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:13" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#13"

/-- RUBI 6.7.8 #14 -/
def rubi678r14 : CRule where
  id := "integration.rubi_6_7_8_r14"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:14"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9830
  description := "RUBI 6.7.8 #14"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:14" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#14"

/-- RUBI 6.7.8 #15 -/
def rubi678r15 : CRule where
  id := "integration.rubi_6_7_8_r15"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9831
  description := "RUBI 6.7.8 #15"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:15" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#15"

/-- RUBI 6.7.8 #16 -/
def rubi678r16 : CRule where
  id := "integration.rubi_6_7_8_r16"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.var "p"))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "n")) (.var "p")) (.pow (.app2 .mul (.var "e") (.var "x")) (.app2 .add (.var "m") (.int 1)))) (.app1 .sinh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n"))))))))) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.var "e")) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "e")) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.var "p")) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.var "x")) (.var "m")) (.pow (.app1 .cosh (.app2 .mul (.var "d") (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .ln (.app2 .mul (.var "c") (.pow (.var "x") (.var "n")))))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "m", "n", "p"]
  conditions := [.int (.var "p"),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "d") (.int 2))) (.pow (.var "n") (.int 2))) (.pow (.var "p") (.int 2))) (.app2 .mul (.int (-1)) (.pow (.app2 .add (.var "m") (.int 1)) (.int 2)))) (.int 0)]
  priority := 9832
  description := "RUBI 6.7.8 #16"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p:16" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.8 u hyper(a+b log(c x^n))^p.m#16"

/-- RUBI 6.7.9 #1 -/
def rubi679r1 : CRule where
  id := "integration.rubi_6_7_9_r1"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9833
  description := "RUBI 6.7.9 #1"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:1" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#1"

/-- RUBI 6.7.9 #10 -/
def rubi679r10 : CRule where
  id := "integration.rubi_6_7_9_r10"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))),
    ("I3", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cosh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "n"),
    .gt (.var "n") (.int 1),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 9834
  description := "RUBI 6.7.9 #10"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:10" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#10"

/-- RUBI 6.7.9 #11 -/
def rubi679r11 : CRule where
  id := "integration.rubi_6_7_9_r11"; legacyId := some "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))) (.var "m")) (.app1 .sech (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app1 .tanh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sinh (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.int (.var "m"),
    .gt (.var "m") (.int 0),
    .int (.var "n"),
    .gt (.var "n") (.int 0)]
  priority := 9835
  description := "RUBI 6.7.9 #11"
  provenance := migrated "rubi:6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions:11" "6 Hyperbolic functions/6.7 Miscellaneous/6.7.9 Active hyperbolic functions.m#11"

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


theorem rubi6113r11_counterexample_real : ¬ rubi6113r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r11.conditions rubi6113r11.body rubi6113r11.result rubi6113r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi6113r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r11_counterexample_complex : ¬ rubi6113r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r11.conditions rubi6113r11.body rubi6113r11.result rubi6113r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi6113r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r12_counterexample_real : ¬ rubi6113r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r12.conditions rubi6113r12.body rubi6113r12.result rubi6113r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi6113r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r12_counterexample_complex : ¬ rubi6113r12.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r12.conditions rubi6113r12.body rubi6113r12.result rubi6113r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi6113r12, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r12.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r12, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r13_counterexample_real : ¬ rubi6113r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r13.conditions rubi6113r13.body rubi6113r13.result rubi6113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi6113r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r13_counterexample_complex : ¬ rubi6113r13.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r13.conditions rubi6113r13.body rubi6113r13.result rubi6113r13.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi6113r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r13.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r14_counterexample_real : ¬ rubi6113r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r14.conditions rubi6113r14.body rubi6113r14.result rubi6113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℝ) (by simp [rubi6113r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r14_counterexample_complex : ¬ rubi6113r14.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r14.conditions rubi6113r14.body rubi6113r14.result rubi6113r14.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) (1 : ℂ) (by simp [rubi6113r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r14.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else if s = "m" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r15_counterexample_real : ¬ rubi6113r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r15.conditions rubi6113r15.body rubi6113r15.result rubi6113r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi6113r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r15_counterexample_complex : ¬ rubi6113r15.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r15.conditions rubi6113r15.body rubi6113r15.result rubi6113r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi6113r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r15.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r16_counterexample_real : ¬ rubi6113r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r16.conditions rubi6113r16.body rubi6113r16.result rubi6113r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi6113r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r16_counterexample_complex : ¬ rubi6113r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r16.conditions rubi6113r16.body rubi6113r16.result rubi6113r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi6113r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "b" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r17_counterexample_real : ¬ rubi6113r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r17.conditions rubi6113r17.body rubi6113r17.result rubi6113r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi6113r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r17_counterexample_complex : ¬ rubi6113r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r17.conditions rubi6113r17.body rubi6113r17.result rubi6113r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi6113r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r18_counterexample_real : ¬ rubi6113r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r18.conditions rubi6113r18.body rubi6113r18.result rubi6113r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi6113r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r18_counterexample_complex : ¬ rubi6113r18.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r18.conditions rubi6113r18.body rubi6113r18.result rubi6113r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) (1 : ℂ) (by simp [rubi6113r18, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r18.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "m" then -3 else if s = "c" ∨ s = "d" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r18, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r7_counterexample_real : ¬ rubi6113r7.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi6113r7.conditions rubi6113r7.body rubi6113r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6113r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6113r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6113r7_counterexample_complex : ¬ rubi6113r7.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi6113r7.conditions rubi6113r7.body rubi6113r7.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi6113r7, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6113r7, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6113r8_counterexample_real : ¬ rubi6113r8.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi6113r8.conditions rubi6113r8.body rubi6113r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6113r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6113r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6113r8_counterexample_complex : ¬ rubi6113r8.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi6113r8.conditions rubi6113r8.body rubi6113r8.result
  refine not_antiderivHoldsUnder (fun s => if s = "d" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi6113r8, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi6113r8, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi6113r9_counterexample_real : ¬ rubi6113r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6113r9.conditions rubi6113r9.body rubi6113r9.result rubi6113r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℝ) (by simp [rubi6113r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6113r9_counterexample_complex : ¬ rubi6113r9.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6113r9.conditions rubi6113r9.body rubi6113r9.result rubi6113r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "e" then 1 else 0) (1 : ℂ) (by simp [rubi6113r9, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6113r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6113r9.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "e" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6113r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6113r9, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6311r11_counterexample_real : ¬ rubi6311r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6311r11.conditions rubi6311r11.body rubi6311r11.result rubi6311r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi6311r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6311r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6311r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6311r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6311r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6311r11_counterexample_complex : ¬ rubi6311r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi6311r11.conditions rubi6311r11.body rubi6311r11.result rubi6311r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi6311r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6311r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6311r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi6311r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6311r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi6311r12_counterexample_real : ¬ rubi6311r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi6311r12.conditions rubi6311r12.body rubi6311r12.result rubi6311r12.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" then 1 else 0) (1 : ℝ) (by simp [rubi6311r12, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi6311r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi6311r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi6311r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi6311r12, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r1_counterexample_real : ¬ rubi676r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r1.conditions rubi676r1.body rubi676r1.result rubi676r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r1_counterexample_complex : ¬ rubi676r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi676r1.conditions rubi676r1.body rubi676r1.result rubi676r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi676r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi676r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r16_counterexample_real : ¬ rubi676r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r16.conditions rubi676r16.body rubi676r16.result rubi676r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r16_counterexample_complex : ¬ rubi676r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi676r16.conditions rubi676r16.body rubi676r16.result rubi676r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi676r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi676r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r17_counterexample_real : ¬ rubi676r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r17.conditions rubi676r17.body rubi676r17.result rubi676r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r17, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r17, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r17_counterexample_complex : ¬ rubi676r17.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi676r17.conditions rubi676r17.body rubi676r17.result rubi676r17.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi676r17, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r17.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi676r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r17, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r18_counterexample_real : ¬ rubi676r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r18.conditions rubi676r18.body rubi676r18.result rubi676r18.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r18, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r18, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r19_counterexample_real : ¬ rubi676r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r19.conditions rubi676r19.body rubi676r19.result rubi676r19.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r19, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r19, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r2_counterexample_real : ¬ rubi676r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r2.conditions rubi676r2.body rubi676r2.result rubi676r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r2, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r2, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r2_counterexample_complex : ¬ rubi676r2.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi676r2.conditions rubi676r2.body rubi676r2.result rubi676r2.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi676r2, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r2.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi676r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r2, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r20_counterexample_real : ¬ rubi676r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r20.conditions rubi676r20.body rubi676r20.result rubi676r20.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r20, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r20, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r21_counterexample_real : ¬ rubi676r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r21.conditions rubi676r21.body rubi676r21.result rubi676r21.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r21, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r21, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r6_counterexample_real : ¬ rubi676r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r6.conditions rubi676r6.body rubi676r6.result rubi676r6.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi676r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r7_counterexample_real : ¬ rubi676r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r7.conditions rubi676r7.body rubi676r7.result rubi676r7.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) (1 : ℝ) (by simp [rubi676r7, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "m" ∨ s = "n" ∨ s = "p" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r7, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r8_counterexample_real : ¬ rubi676r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r8.conditions rubi676r8.body rubi676r8.result rubi676r8.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r8, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r8, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi676r9_counterexample_real : ¬ rubi676r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi676r9.conditions rubi676r9.body rubi676r9.result rubi676r9.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi676r9, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi676r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi676r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi676r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi676r9, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi677r31_counterexample_real : ¬ rubi677r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi677r31.conditions rubi677r31.body rubi677r31.result rubi677r31.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" then -1 else if s = "F" ∨ s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" then 1 else 0) (-1 : ℝ) (by simp [rubi677r31, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi677r31.integrals[0]!, by simp [rubi677r31], ?_⟩
  intro h
  simp [rubi677r31, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi677r31_counterexample_complex : ¬ rubi677r31.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi677r31.conditions rubi677r31.body rubi677r31.result rubi677r31.integrals
  refine not_antiderivRecHolds_integrand (fun s => if s = "f" then -1 else if s = "F" ∨ s = "a" ∨ s = "c" ∨ s = "d" ∨ s = "e" ∨ s = "g" then 1 else 0) (-1 : ℂ) (by simp [rubi677r31, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ⟨rubi677r31.integrals[0]!, by simp [rubi677r31], ?_⟩
  intro h
  simp [rubi677r31, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi677r5_counterexample_real : ¬ rubi677r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi677r5.conditions rubi677r5.body rubi677r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi677r5, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi677r5, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi677r5_counterexample_complex : ¬ rubi677r5.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi677r5.conditions rubi677r5.body rubi677r5.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi677r5, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi677r5, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi677r6_counterexample_real : ¬ rubi677r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi677r6.conditions rubi677r6.body rubi677r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi677r6, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi677r6, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi677r6_counterexample_complex : ¬ rubi677r6.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi677r6.conditions rubi677r6.body rubi677r6.result
  refine not_antiderivHoldsUnder (fun s => if s = "F" ∨ s = "c" ∨ s = "d" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi677r6, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi677r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi677r6, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi678r13_counterexample_real : ¬ rubi678r13.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi678r13.conditions rubi678r13.body rubi678r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi678r13, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi678r13, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi678r13_counterexample_complex : ¬ rubi678r13.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi678r13.conditions rubi678r13.body rubi678r13.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi678r13, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi678r13, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi678r14_counterexample_real : ¬ rubi678r14.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi678r14.conditions rubi678r14.body rubi678r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℝ) (by simp [rubi678r14, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi678r14, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi678r14_counterexample_complex : ¬ rubi678r14.Holds .complex := by
  show ¬ AntiderivHoldsUnder Interp.complex "x" rubi678r14.conditions rubi678r14.body rubi678r14.result
  refine not_antiderivHoldsUnder (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else 0) (1 : ℂ) (by simp [rubi678r14, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) ?_
  intro h
  simp [rubi678r14, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] at h <;> norm_num at h

theorem rubi678r15_counterexample_real : ¬ rubi678r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi678r15.conditions rubi678r15.body rubi678r15.result rubi678r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi678r15, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi678r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi678r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi678r15, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi678r15_counterexample_complex : ¬ rubi678r15.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi678r15.conditions rubi678r15.body rubi678r15.result rubi678r15.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi678r15, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi678r15.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi678r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi678r15, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi678r16_counterexample_real : ¬ rubi678r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi678r16.conditions rubi678r16.body rubi678r16.result rubi678r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) (1 : ℝ) (by simp [rubi678r16, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi678r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi678r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi678r16, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi678r16_counterexample_complex : ¬ rubi678r16.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi678r16.conditions rubi678r16.body rubi678r16.result rubi678r16.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) (1 : ℂ) (by simp [rubi678r16, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi678r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi678r16.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "b" ∨ s = "c" ∨ s = "d" ∨ s = "m" then 1 else if s = "p" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi678r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi678r16, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r1_counterexample_real : ¬ rubi679r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r1.conditions rubi679r1.body rubi679r1.result rubi679r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r1, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r1, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r1_counterexample_complex : ¬ rubi679r1.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r1.conditions rubi679r1.body rubi679r1.result rubi679r1.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi679r1, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r1.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r1, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r10_counterexample_real : ¬ rubi679r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r10.conditions rubi679r10.body rubi679r10.result rubi679r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℝ) (by simp [rubi679r10, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r10, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r10_counterexample_complex : ¬ rubi679r10.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r10.conditions rubi679r10.body rubi679r10.result rubi679r10.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) (1 : ℂ) (by simp [rubi679r10, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r10.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" then 1 else if s = "n" then 2 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r10, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r11_counterexample_real : ¬ rubi679r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi679r11.conditions rubi679r11.body rubi679r11.result rubi679r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℝ) (by simp [rubi679r11, Cond.Holds, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp only [rubi679r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r11, Defined, eval, Interp.real, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

theorem rubi679r11_counterexample_complex : ¬ rubi679r11.Holds .complex := by
  show ¬ AntiderivRecHolds Interp.complex "x" rubi679r11.conditions rubi679r11.body rubi679r11.result rubi679r11.integrals
  refine not_antiderivRecHolds_result (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) (1 : ℂ) (by simp [rubi679r11, Cond.Holds, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (Eventually.of_forall fun w => by simp [rubi679r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg] <;> first | positivity | (exact ⟨2, by rw [one_add_one_eq_two]; exact iv2, by norm_num⟩) | (norm_num <;> first | exact ⟨_, ivm6⟩ | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℂ) + 1 = 2 by norm_num]; exact iv2) | (refine ⟨2, ?_, by norm_num⟩; rw [show (1:ℝ) + 1 = 2 by norm_num]; exact iv2) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2)) | (intro h; have h2 := congrArg Complex.exp h; rw [Complex.exp_log (by norm_num), Complex.exp_zero] at h2; norm_num at h2))
    (fun h w => w * (((rubi679r11.integrals.lookup h).map (eval Interp.complex (Function.update (fun s => if s = "a" ∨ s = "e" ∨ s = "f" ∨ s = "m" ∨ s = "n" then 1 else 0) "x" (1 : ℂ)))).getD 0)) ?_ ?_
  · simp only [rubi679r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros
    all_goals (simp [List.lookup]; exact hasDerivAt_mul_const _)
  · intro h
    simp [rubi679r11, Defined, eval, Interp.complex, iv0, iv1, iv2, iv3, iv4, ivm1, ivm2, ivm3, ivm4, ivm5, ivm6, ivm7, ivm8, ivm9, ivm10, ivm11, ivm12, ivnat, ivneg, recEnv] at h <;> norm_num at h

end OSR.IntegrationRec123
