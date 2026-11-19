import OSR.IntegrationRec91

/-!
# Integration (RUBI): refutations of rules written with Simp or compound conditions

RUBI rules transcribed as stated.  Each is refuted by an explicit assignment:
the conditions hold and the integrand is defined near a point where the
result or a residual integrand is not (RUBI excludes these cases by its rule
order).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace OSR.IntegrationRec171

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 5.1.4 #7 -/
def rubi514r7 : CRule where
  id := "integration.rubi_5_1_4_r7"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12300
  description := "RUBI 5.1.4 #7"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:7" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#7"

/-- RUBI 5.1.4 #21 -/
def rubi514r21 : CRule where
  id := "integration.rubi_5_1_4_r21"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:21"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12301
  description := "RUBI 5.1.4 #21"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:21" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#21"

/-- RUBI 5.1.4 #28 -/
def rubi514r28 : CRule where
  id := "integration.rubi_5_1_4_r28"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12302
  description := "RUBI 5.1.4 #28"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:28" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#28"

/-- RUBI 5.1.4 #33 -/
def rubi514r33 : CRule where
  id := "integration.rubi_5_1_4_r33"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12303
  description := "RUBI 5.1.4 #33"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:33" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#33"

/-- RUBI 7.1.4 #15 -/
def rubi714r15 : CRule where
  id := "integration.rubi_7_1_4_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "n"),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12304
  description := "RUBI 7.1.4 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:15" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#15"

/-- RUBI 7.1.3 #2 -/
def rubi713r2 : CRule where
  id := "integration.rubi_7_1_3_r2"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .ne (.var "n") (.int (-1))]
  priority := 12305
  description := "RUBI 7.1.3 #2"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:2" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n.m#2"



/-- RUBI 5.1.3 #1 -/
def rubi513r1 : CRule where
  id := "integration.rubi_5_1_3_r1"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x")))))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)]
  priority := 12308
  description := "RUBI 5.1.3 #1"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:1" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#1"

/-- RUBI 5.1.3 #15 -/
def rubi513r15 : CRule where
  id := "integration.rubi_5_1_3_r15"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12309
  description := "RUBI 5.1.3 #15"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:15" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#15"

/-- RUBI 5.1.4 #8 -/
def rubi514r8 : CRule where
  id := "integration.rubi_5_1_4_r8"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12310
  description := "RUBI 5.1.4 #8"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:8" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#8"

/-- RUBI 5.1.4 #22 -/
def rubi514r22 : CRule where
  id := "integration.rubi_5_1_4_r22"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12311
  description := "RUBI 5.1.4 #22"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:22" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#22"

/-- RUBI 5.1.4 #29 -/
def rubi514r29 : CRule where
  id := "integration.rubi_5_1_4_r29"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12312
  description := "RUBI 5.1.4 #29"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:29" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#29"

/-- RUBI 5.1.4 #34 -/
def rubi514r34 : CRule where
  id := "integration.rubi_5_1_4_r34"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12313
  description := "RUBI 5.1.4 #34"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:34" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#34"

/-- RUBI 7.1.4 #2 -/
def rubi714r2 : CRule where
  id := "integration.rubi_7_1_4_r2"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12314
  description := "RUBI 7.1.4 #2"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:2" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#2"

/-- RUBI 7.1.4 #16 -/
def rubi714r16 : CRule where
  id := "integration.rubi_7_1_4_r16"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "n"),
    .int (.app2 .mul (.int 2) (.var "p")),
    .gt (.app2 .mul (.int 2) (.var "p")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int (-3))]
  priority := 12315
  description := "RUBI 7.1.4 #16"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:16" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#16"

/-- RUBI 7.2.3 #5 -/
def rubi723r5 : CRule where
  id := "integration.rubi_7_2_3_r5"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.int 2)) (.int (-1))))) (.app2 .mul (.app2 .root (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "n"]
  conditions := [.eq (.var "e1") (.app2 .mul (.var "c") (.var "d1")),
    .eq (.var "e2") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d2")),
    .ne (.var "n") (.int (-1))]
  priority := 12316
  description := "RUBI 7.2.3 #5"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:5" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m#5"

/-- RUBI 7.2.4 #24 -/
def rubi724r24 : CRule where
  id := "integration.rubi_7_2_4_r24"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p"))) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12317
  description := "RUBI 7.2.4 #24"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:24" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#24"

/-- RUBI 5.1.3 #2 -/
def rubi513r2 : CRule where
  id := "integration.rubi_5_1_3_r2"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "b") (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .root (.var "d") (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0)]
  priority := 12318
  description := "RUBI 5.1.3 #2"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:2" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#2"

/-- RUBI 5.1.3 #16 -/
def rubi513r16 : CRule where
  id := "integration.rubi_5_1_3_r16"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:16"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12319
  description := "RUBI 5.1.3 #16"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:16" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#16"

/-- RUBI 5.1.4 #23 -/
def rubi514r23 : CRule where
  id := "integration.rubi_5_1_4_r23"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12320
  description := "RUBI 5.1.4 #23"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:23" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#23"

/-- RUBI 5.1.4 #30 -/
def rubi514r30 : CRule where
  id := "integration.rubi_5_1_4_r30"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12321
  description := "RUBI 5.1.4 #30"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:30" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#30"

/-- RUBI 5.1.4 #39 -/
def rubi514r39 : CRule where
  id := "integration.rubi_5_1_4_r39"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12322
  description := "RUBI 5.1.4 #39"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:39" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#39"

/-- RUBI 7.1.4 #4 -/
def rubi714r4 : CRule where
  id := "integration.rubi_7_1_4_r4"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12323
  description := "RUBI 7.1.4 #4"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:4" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#4"

/-- RUBI 7.1.4 #11 -/
def rubi714r11 : CRule where
  id := "integration.rubi_7_1_4_r11"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12324
  description := "RUBI 7.1.4 #11"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:11" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#11"

/-- RUBI 7.1.4 #17 -/
def rubi714r17 : CRule where
  id := "integration.rubi_7_1_4_r17"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12325
  description := "RUBI 7.1.4 #17"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:17" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#17"

/-- RUBI 7.2.4 #3 -/
def rubi724r3 : CRule where
  id := "integration.rubi_7_2_4_r3"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p"))) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12326
  description := "RUBI 7.2.4 #3"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:3" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#3"

/-- RUBI 7.2.4 #18 -/
def rubi724r18 : CRule where
  id := "integration.rubi_7_2_4_r18"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:18"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p"))) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12327
  description := "RUBI 7.2.4 #18"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:18" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#18"

/-- RUBI 7.2.4 #25 -/
def rubi724r25 : CRule where
  id := "integration.rubi_7_2_4_r25"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "e1") (.var "e2")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.app2 .mul (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "f", "p", "m", "n"]
  conditions := [.eq (.var "e1") (.app2 .mul (.var "c") (.var "d1")),
    .eq (.var "e2") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d2")),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12328
  description := "RUBI 7.2.4 #25"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:25" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#25"

/-- RUBI 5.1.3 #4 -/
def rubi513r4 : CRule where
  id := "integration.rubi_5_1_3_r4"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:4"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 12329
  description := "RUBI 5.1.3 #4"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:4" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#4"

/-- RUBI 5.1.4 #4 -/
def rubi514r4 : CRule where
  id := "integration.rubi_5_1_4_r4"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12330
  description := "RUBI 5.1.4 #4"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:4" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#4"

/-- RUBI 5.1.4 #27 -/
def rubi514r27 : CRule where
  id := "integration.rubi_5_1_4_r27"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12331
  description := "RUBI 5.1.4 #27"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:27" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#27"

/-- RUBI 5.1.4 #32 -/
def rubi514r32 : CRule where
  id := "integration.rubi_5_1_4_r32"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .int (.app2 .mul (.int 2) (.var "p")),
    .gt (.app2 .mul (.int 2) (.var "p")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int (-3))]
  priority := 12332
  description := "RUBI 5.1.4 #32"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:32" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#32"

/-- RUBI 7.1.4 #14 -/
def rubi714r14 : CRule where
  id := "integration.rubi_7_1_4_r14"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "p", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0)]
  priority := 12333
  description := "RUBI 7.1.4 #14"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:14" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#14"

/-- RUBI 7.1.3 #1 -/
def rubi713r1 : CRule where
  id := "integration.rubi_7_1_3_r1"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.var "c")) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.app1 .ln (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x")))))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d"))]
  priority := 12334
  description := "RUBI 7.1.3 #1"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:1" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n.m#1"

/-- RUBI 7.1.3 #8 -/
def rubi713r8 : CRule where
  id := "integration.rubi_7_1_3_r8"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "n")]
  priority := 12335
  description := "RUBI 7.1.3 #8"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n:8" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n.m#8"


/-- RUBI 7.2.4 #6 -/
def rubi724r6 : CRule where
  id := "integration.rubi_7_2_4_r6"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p"))) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12337
  description := "RUBI 7.2.4 #6"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:6" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#6"


/-- RUBI 5.1.3 #3 -/
def rubi513r3 : CRule where
  id := "integration.rubi_5_1_3_r3"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:3"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .ne (.var "n") (.int (-1))]
  priority := 12339
  description := "RUBI 5.1.3 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n:3" "5 Inverse trig functions/5.1 Inverse sine/5.1.3 (d+e x^2)^p (a+b arcsin(c x))^n.m#3"

/-- RUBI 5.1.4 #3 -/
def rubi514r3 : CRule where
  id := "integration.rubi_5_1_4_r3"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12340
  description := "RUBI 5.1.4 #3"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:3" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#3"

/-- RUBI 5.1.4 #24 -/
def rubi514r24 : CRule where
  id := "integration.rubi_5_1_4_r24"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12341
  description := "RUBI 5.1.4 #24"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:24" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#24"

/-- RUBI 5.1.4 #31 -/
def rubi514r31 : CRule where
  id := "integration.rubi_5_1_4_r31"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsin (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .int (.app2 .mul (.int 2) (.var "p")),
    .gt (.app2 .mul (.int 2) (.var "p")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 1)) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int (-3))]
  priority := 12342
  description := "RUBI 5.1.4 #31"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:31" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#31"

/-- RUBI 5.1.4 #40 -/
def rubi514r40 : CRule where
  id := "integration.rubi_5_1_4_r40"; legacyId := some "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccos (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12343
  description := "RUBI 5.1.4 #40"
  provenance := migrated "rubi:5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n:40" "5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m#40"

/-- RUBI 7.1.4 #12 -/
def rubi714r12 : CRule where
  id := "integration.rubi_7_1_4_r12"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "f") (.int 2))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "e")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "f")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.var "n") (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12344
  description := "RUBI 7.1.4 #12"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:12" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#12"

/-- RUBI 7.1.4 #20 -/
def rubi714r20 : CRule where
  id := "integration.rubi_7_1_4_r20"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "f")) (.var "m")) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.pow (.var "c") (.int 2)) (.pow (.var "x") (.int 2)))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.int 2)) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arcsinh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.var "e") (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")),
    .gt (.int (-1)) (.var "n")]
  priority := 12345
  description := "RUBI 7.1.4 #20"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n:20" "7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m#20"


/-- RUBI 7.2.3 #15 -/
def rubi723r15 : CRule where
  id := "integration.rubi_7_2_3_r15"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.int 2)) (.app2 .root (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.int 2))) (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 1))) (.pow (.app2 .mul (.var "b") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d") (.app2 .mul (.var "e") (.pow (.var "x") (.int 2)))) (.var "p")) (.pow (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p"))) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "p", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "d")) (.var "e")) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .int (.app2 .mul (.int 2) (.var "p"))]
  priority := 12347
  description := "RUBI 7.2.3 #15"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n:15" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m#15"

/-- RUBI 7.2.4 #4 -/
def rubi724r4 : CRule where
  id := "integration.rubi_7_2_4_r4"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.var "x") (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "e1")) (.var "e2")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "n")) (.pow (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.app2 .mul (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1)))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "p", "n"]
  conditions := [.eq (.var "e1") (.app2 .mul (.var "c") (.var "d1")),
    .eq (.var "e2") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d2")),
    .gt (.var "n") (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12348
  description := "RUBI 7.2.4 #4"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:4" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#4"

/-- RUBI 7.2.4 #19 -/
def rubi724r19 : CRule where
  id := "integration.rubi_7_2_4_r19"; legacyId := some "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.var "m")) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d1") (.var "d2")) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int 2) (.var "p"))) (.int 3))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.app2 .mul (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p")) (.pow (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.var "p")) (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.var "d1") (.app2 .mul (.var "e1") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "d2") (.app2 .mul (.var "e2") (.var "x"))) (.var "p"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "f") (.var "x")) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.int 1) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.int (-1)) (.app2 .mul (.var "c") (.var "x"))) (.app2 .add (.var "p") (.app2 .mul (.int 1) (.pow (.int 2) (.int (-1))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .arccosh (.app2 .mul (.var "c") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "c", "d1", "e1", "d2", "e2", "f", "p", "m", "n"]
  conditions := [.eq (.var "e1") (.app2 .mul (.var "c") (.var "d1")),
    .eq (.var "e2") (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "d2")),
    .gt (.var "n") (.int 0),
    .int (.var "m"),
    .gt (.int (-1)) (.var "m")]
  priority := 12349
  description := "RUBI 7.2.4 #19"
  provenance := migrated "rubi:7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n:19" "7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m#19"

/-! ## Refutations -/

theorem rubi514r7_counterexample_real : ¬ rubi514r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r7.conditions rubi514r7.body rubi514r7.result rubi514r7.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "f" then ((1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "f" then ((1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r21_counterexample_real : ¬ rubi514r21.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r21.conditions rubi514r21.body rubi514r21.result rubi514r21.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) (0.5 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (0.5 : ℝ) - 1/16 < 0.5 by norm_num) (show (0.5 : ℝ) < 0.5 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r21.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (0.5 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r21, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r21, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r28_counterexample_real : ¬ rubi514r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r28.conditions rubi514r28.body rubi514r28.result rubi514r28.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r28, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r33_counterexample_real : ¬ rubi514r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r33.conditions rubi514r33.body rubi514r33.result rubi514r33.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r33, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r15_counterexample_real : ¬ rubi714r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r15.conditions rubi714r15.body rubi714r15.result rubi714r15.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi713r2_counterexample_real : ¬ rubi713r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi713r2.conditions rubi713r2.body rubi713r2.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "d" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi713r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi713r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi713r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi713r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi513r1_counterexample_real : ¬ rubi513r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi513r1.conditions rubi513r1.body rubi513r1.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi513r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi513r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi513r15_counterexample_real : ¬ rubi513r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi513r15.conditions rubi513r15.body rubi513r15.result rubi513r15.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi513r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi513r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi513r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi513r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r8_counterexample_real : ¬ rubi514r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r8.conditions rubi514r8.body rubi514r8.result rubi514r8.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "f" then ((1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "f" then ((1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r22_counterexample_real : ¬ rubi514r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r22.conditions rubi514r22.body rubi514r22.result rubi514r22.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) (0.5 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (0.5 : ℝ) - 1/16 < 0.5 by norm_num) (show (0.5 : ℝ) < 0.5 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (0.5 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r22, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r29_counterexample_real : ¬ rubi514r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r29.conditions rubi514r29.body rubi514r29.result rubi514r29.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r34_counterexample_real : ¬ rubi514r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r34.conditions rubi514r34.body rubi514r34.result rubi514r34.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r34, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r2_counterexample_real : ¬ rubi714r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r2.conditions rubi714r2.body rubi714r2.result rubi714r2.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r16_counterexample_real : ¬ rubi714r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r16.conditions rubi714r16.body rubi714r16.result rubi714r16.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (-3 : ℝ) else if s = "n" then (-3 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi714r16, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi714r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi723r5_counterexample_real : ¬ rubi723r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi723r5.conditions rubi723r5.body rubi723r5.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "c" then (1 : ℝ) else if s = "d1" then (4 : ℝ) else if s = "d2" then ((-1 : ℝ) / 2) else if s = "e1" then (4 : ℝ) else if s = "e2" then ((1 : ℝ) / 2) else if s = "n" then (1 : ℝ) else 0) (2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi723r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (2 : ℝ) - 1/16 < 2 by norm_num) (show (2 : ℝ) < 2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi723r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi723r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi723r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi724r24_counterexample_real : ¬ rubi724r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r24.conditions rubi724r24.body rubi724r24.result rubi724r24.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (2 : ℝ) else 0) (2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (2 : ℝ) - 1/16 < 2 by norm_num) (show (2 : ℝ) < 2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (2 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi513r2_counterexample_real : ¬ rubi513r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi513r2.conditions rubi513r2.body rubi513r2.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "b" then (-1 : ℝ) else if s = "d" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi513r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi513r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi513r16_counterexample_real : ¬ rubi513r16.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi513r16.conditions rubi513r16.body rubi513r16.result rubi513r16.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi513r16.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi513r16, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi513r16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi513r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r23_counterexample_real : ¬ rubi514r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r23.conditions rubi514r23.body rubi514r23.result rubi514r23.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r30_counterexample_real : ¬ rubi514r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r30.conditions rubi514r30.body rubi514r30.result rubi514r30.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (-2 : ℝ) else if s = "f" then (4 : ℝ) else if s = "m" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r30, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r39_counterexample_real : ¬ rubi514r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r39.conditions rubi514r39.body rubi514r39.result rubi514r39.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (4 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi514r39, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi514r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi714r4_counterexample_real : ¬ rubi714r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r4.conditions rubi714r4.body rubi714r4.result rubi714r4.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r11_counterexample_real : ¬ rubi714r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r11.conditions rubi714r11.body rubi714r11.result rubi714r11.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r17_counterexample_real : ¬ rubi714r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r17.conditions rubi714r17.body rubi714r17.result rubi714r17.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "d" then (3 : ℝ) else if s = "m" then (3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r3_counterexample_real : ¬ rubi724r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r3.conditions rubi724r3.body rubi724r3.result rubi724r3.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) (-1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) - 1/16 < -1 by norm_num) (show (-1 : ℝ) < -1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (-3 : ℝ) else if s = "n" then (1 : ℝ) else 0) "x" (-1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r18_counterexample_real : ¬ rubi724r18.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r18.conditions rubi724r18.body rubi724r18.result rubi724r18.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) (2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (2 : ℝ) - 1/16 < 2 by norm_num) (show (2 : ℝ) < 2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r18.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (1 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (2 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r18, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r25_counterexample_real : ¬ rubi724r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r25.conditions rubi724r25.body rubi724r25.result rubi724r25.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else if s = "c" then (2 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (1 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else if s = "c" then (2 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (1 : ℝ) else if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi513r4_counterexample_real : ¬ rubi513r4.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi513r4.conditions rubi513r4.body rubi513r4.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "d" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi513r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi513r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi514r4_counterexample_real : ¬ rubi514r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r4.conditions rubi514r4.body rubi514r4.result rubi514r4.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r27_counterexample_real : ¬ rubi514r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r27.conditions rubi514r27.body rubi514r27.result rubi514r27.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r32_counterexample_real : ¬ rubi514r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r32.conditions rubi514r32.body rubi514r32.result rubi514r32.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (-3 : ℝ) else if s = "n" then (-3 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi514r32, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi514r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi714r14_counterexample_real : ¬ rubi714r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r14.conditions rubi714r14.body rubi714r14.result rubi714r14.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (4 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi713r1_counterexample_real : ¬ rubi713r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi713r1.conditions rubi713r1.body rubi713r1.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi713r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi713r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi713r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi713r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi713r8_counterexample_real : ¬ rubi713r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi713r8.conditions rubi713r8.body rubi713r8.result rubi713r8.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi713r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi713r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi713r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi713r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi713r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi713r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r6_counterexample_real : ¬ rubi724r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r6.conditions rubi724r6.body rubi724r6.result rubi724r6.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) (-1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) - 1/16 < -1 by norm_num) (show (-1 : ℝ) < -1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "c" then (-3 : ℝ) else if s = "f" then (-2 : ℝ) else if s = "m" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (-1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi513r3_counterexample_real : ¬ rubi513r3.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi513r3.conditions rubi513r3.body rubi513r3.result
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivHoldsUnder (fun s => if s = "d" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi513r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi513r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi513r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi513r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi514r3_counterexample_real : ¬ rubi514r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r3.conditions rubi514r3.body rubi514r3.result rubi514r3.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r24_counterexample_real : ¬ rubi514r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r24.conditions rubi514r24.body rubi514r24.result rubi514r24.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi514r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi514r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi514r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi514r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi514r31_counterexample_real : ¬ rubi514r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r31.conditions rubi514r31.body rubi514r31.result rubi514r31.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (-3 : ℝ) else if s = "n" then (-3 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi514r31, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi514r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi514r40_counterexample_real : ¬ rubi514r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi514r40.conditions rubi514r40.body rubi514r40.result rubi514r40.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (4 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi514r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi514r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi514r40, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi514r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi714r12_counterexample_real : ¬ rubi714r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r12.conditions rubi714r12.body rubi714r12.result rubi714r12.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi714r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (2 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi714r12, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi714r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi714r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi714r20_counterexample_real : ¬ rubi714r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi714r20.conditions rubi714r20.body rubi714r20.result rubi714r20.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (4 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi714r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi714r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi714r20, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi714r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi723r15_counterexample_real : ¬ rubi723r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi723r15.conditions rubi723r15.body rubi723r15.result rubi723r15.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "c" then (-2 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (-1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi723r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) - 1/16 < -1 by norm_num) (show (-1 : ℝ) < -1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi723r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi723r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "c" then (-2 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (-1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi723r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi723r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi723r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r4_counterexample_real : ¬ rubi724r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r4.conditions rubi724r4.body rubi724r4.result rubi724r4.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "c" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) (-1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) - 1/16 < -1 by norm_num) (show (-1 : ℝ) < -1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "c" then (-3 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (-1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi724r19_counterexample_real : ¬ rubi724r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi724r19.conditions rubi724r19.body rubi724r19.result rubi724r19.integrals
  have ivm12 : intValue? (-12 : ℝ) = some (-12) := (intValue?_eq _ _).2 (by norm_num)
  have ivm11 : intValue? (-11 : ℝ) = some (-11) := (intValue?_eq _ _).2 (by norm_num)
  have ivm10 : intValue? (-10 : ℝ) = some (-10) := (intValue?_eq _ _).2 (by norm_num)
  have ivm9 : intValue? (-9 : ℝ) = some (-9) := (intValue?_eq _ _).2 (by norm_num)
  have ivm8 : intValue? (-8 : ℝ) = some (-8) := (intValue?_eq _ _).2 (by norm_num)
  have ivm7 : intValue? (-7 : ℝ) = some (-7) := (intValue?_eq _ _).2 (by norm_num)
  have ivm6 : intValue? (-6 : ℝ) = some (-6) := (intValue?_eq _ _).2 (by norm_num)
  have ivm5 : intValue? (-5 : ℝ) = some (-5) := (intValue?_eq _ _).2 (by norm_num)
  have ivm4 : intValue? (-4 : ℝ) = some (-4) := (intValue?_eq _ _).2 (by norm_num)
  have ivm3 : intValue? (-3 : ℝ) = some (-3) := (intValue?_eq _ _).2 (by norm_num)
  have ivm2 : intValue? (-2 : ℝ) = some (-2) := (intValue?_eq _ _).2 (by norm_num)
  have ivm1 : intValue? (-1 : ℝ) = some (-1) := (intValue?_eq _ _).2 (by norm_num)
  have iv0 : intValue? (0 : ℝ) = some (0) := (intValue?_eq _ _).2 (by norm_num)
  have iv1 : intValue? (1 : ℝ) = some (1) := (intValue?_eq _ _).2 (by norm_num)
  have iv2 : intValue? (2 : ℝ) = some (2) := (intValue?_eq _ _).2 (by norm_num)
  have iv3 : intValue? (3 : ℝ) = some (3) := (intValue?_eq _ _).2 (by norm_num)
  have iv4 : intValue? (4 : ℝ) = some (4) := (intValue?_eq _ _).2 (by norm_num)
  have iv5 : intValue? (5 : ℝ) = some (5) := (intValue?_eq _ _).2 (by norm_num)
  have iv6 : intValue? (6 : ℝ) = some (6) := (intValue?_eq _ _).2 (by norm_num)
  have iv7 : intValue? (7 : ℝ) = some (7) := (intValue?_eq _ _).2 (by norm_num)
  have iv8 : intValue? (8 : ℝ) = some (8) := (intValue?_eq _ _).2 (by norm_num)
  have iv9 : intValue? (9 : ℝ) = some (9) := (intValue?_eq _ _).2 (by norm_num)
  have iv10 : intValue? (10 : ℝ) = some (10) := (intValue?_eq _ _).2 (by norm_num)
  have iv11 : intValue? (11 : ℝ) = some (11) := (intValue?_eq _ _).2 (by norm_num)
  have iv12 : intValue? (12 : ℝ) = some (12) := (intValue?_eq _ _).2 (by norm_num)
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "d2" then (-3 : ℝ) else if s = "e2" then (-3 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) (-2 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi724r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (-2 : ℝ) - 1/16 < -2 by norm_num) (show (-2 : ℝ) < -2 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi724r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi724r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "d2" then (-3 : ℝ) else if s = "e2" then (-3 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (-2 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (-2 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi724r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi724r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi724r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

end OSR.IntegrationRec171
