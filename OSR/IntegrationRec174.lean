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

namespace OSR.IntegrationRec174

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/

/-- RUBI 4.1.2.2 #22 -/
def rubi4122r22 : CRule where
  id := "integration.rubi_4_1_2_2_r22"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:22"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)))) (.int 0)]
  priority := 12800
  description := "RUBI 4.1.2.2 #22"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:22" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#22"


/-- RUBI 4.1.2.2 #38 -/
def rubi4122r38 : CRule where
  id := "integration.rubi_4_1_2_2_r38"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "f")) (.var "g")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .mul (.int 2) (.pow (.var "g") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))))]
  independent := ["a", "b", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "p"))) (.int 0)]
  priority := 12802
  description := "RUBI 4.1.2.2 #38"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:38" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#38"

/-- RUBI 4.1.2.2 #48 -/
def rubi4122r48 : CRule where
  id := "integration.rubi_4_1_2_2_r48"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:48"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 4)) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-2)) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "a") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 2))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 2)))) (.app2 .add (.int 1) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))]
  independent := ["a", "b", "d", "e", "f", "n", "m"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12803
  description := "RUBI 4.1.2.2 #48"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:48" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#48"


/-- RUBI 4.1.1.1 #2 -/
def rubi4111r2 : CRule where
  id := "integration.rubi_4_1_1_1_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:2"
  shape := .antideriv; x := "x"
  body := (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.app2 .mul (.var "d") (.var "x")) (.pow (.int 2) (.int (-1)))))) (.int 2))
  result := (.app2 .add (.app2 .mul (.var "x") (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .sin (.app2 .add (.app2 .mul (.int 2) (.var "c")) (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1)))))
  independent := ["c", "d"]
  priority := 12805
  description := "RUBI 4.1.1.1 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:2" "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#2"

/-- RUBI 4.1.1.1 #11 -/
def rubi4111r11 : CRule where
  id := "integration.rubi_4_1_1_1_r11"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:11"
  shape := .antideriv; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.int 2) (.pow (.var "a") (.int 2))) (.pow (.var "b") (.int 2))) (.var "x")) (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.var "d") (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1)))))
  independent := ["a", "b", "c", "d"]
  priority := 12806
  description := "RUBI 4.1.1.1 #11"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:11" "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#11"



/-- RUBI 4.1.4.1 #1 -/
def rubi4141r1 : CRule where
  id := "integration.rubi_4_1_4_1_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.app2 .add (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "b") (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "B") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["b", "e", "f", "B", "C", "m"]
  priority := 12809
  description := "RUBI 4.1.4.1 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):1" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#1"

/-- RUBI 4.1.4.1 #10 -/
def rubi4141r10 : CRule where
  id := "integration.rubi_4_1_4_1_r10"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.var "b") (.var "C"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.var "m") (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "B", "C", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12810
  description := "RUBI 4.1.4.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):10" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#10"






/-- RUBI 4.1.6 #14 -/
def rubi416r14 : CRule where
  id := "integration.rubi_4_1_6_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:14"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.var "n") (.int 2))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.app2 .add (.var "n") (.int 2))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1))))]
  priority := 12816
  description := "RUBI 4.1.6 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:14" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#14"

/-- RUBI 4.1.6 #22 -/
def rubi416r22 : CRule where
  id := "integration.rubi_4_1_6_r22"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:22"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "C"))) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "C"))) (.int 0)]
  priority := 12817
  description := "RUBI 4.1.6 #22"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:22" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#22"

/-- RUBI 4.1.6 #27 -/
def rubi416r27 : CRule where
  id := "integration.rubi_4_1_6_r27"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "C", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 12818
  description := "RUBI 4.1.6 #27"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:27" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#27"

/-- RUBI 4.1.6 #32 -/
def rubi416r32 : CRule where
  id := "integration.rubi_4_1_6_r32"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:32"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "b")) (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "C")) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "A", "C", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)]
  priority := 12819
  description := "RUBI 4.1.6 #32"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:32" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#32"

/-- RUBI 4.1.6 #37 -/
def rubi416r37 : CRule where
  id := "integration.rubi_4_1_6_r37"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:37"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.var "c") (.var "A")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A"))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)]
  priority := 12820
  description := "RUBI 4.1.6 #37"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:37" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#37"

/-- RUBI 4.1.6 #42 -/
def rubi416r42 : CRule where
  id := "integration.rubi_4_1_6_r42"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:42"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A"))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.var "A")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C")))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "n") (.int 2))) (.var "b")) (.var "A")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .add (.var "n") (.int 2)) (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A")))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "A", "C", "n"]
  conditions := [.gt (.int (-1)) (.var "n"),
    .ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-2))]
  priority := 12821
  description := "RUBI 4.1.6 #42"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:42" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#42"


/-- RUBI 4.3.3.1 #23 -/
def rubi4331r23 : CRule where
  id := "integration.rubi_4_3_3_1_r23"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "B") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.var "n"))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.var "m") (.var "n")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.var "c")) (.app2 .add (.var "m") (.var "n"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "n"))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.var "c"))) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.var "d"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.var "d"))) (.app2 .add (.var "m") (.var "n"))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "d")) (.app2 .add (.var "m") (.var "n"))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "n"))))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 12823
  description := "RUBI 4.3.3.1 #23"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):23" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#23"

/-- RUBI 4.3.1.1 #1 -/
def rubi4311r1 : CRule where
  id := "integration.rubi_4_3_1_1_r1"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))))]
  independent := ["b", "c", "d", "n"]
  conditions := [.gt (.var "n") (.int 1)]
  priority := 12824
  description := "RUBI 4.3.1.1 #1"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:1" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#1"

/-- RUBI 4.3.1.1 #10 -/
def rubi4311r10 : CRule where
  id := "integration.rubi_4_3_1_1_r10"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 12825
  description := "RUBI 4.3.1.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:10" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#10"


/-- RUBI 4.3.1.2 #25 -/
def rubi4312r25 : CRule where
  id := "integration.rubi_4_3_1_2_r25"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 1)]
  priority := 12827
  description := "RUBI 4.3.1.2 #25"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:25" "4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m#25"


/-- RUBI 4.3.4.1 #3 -/
def rubi4341r3 : CRule where
  id := "integration.rubi_4_3_4_1_r3"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "B", "C", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 12829
  description := "RUBI 4.3.4.1 #3"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):3" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#3"

/-- RUBI 4.3.2.1 #4 -/
def rubi4321r4 : CRule where
  id := "integration.rubi_4_3_2_1_r4"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d"))) (.var "x")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.var "f") (.int (-1))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.var "I1")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0)]
  priority := 12830
  description := "RUBI 4.3.2.1 #4"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:4" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#4"

/-- RUBI 4.3.2.1 #19 -/
def rubi4321r19 : CRule where
  id := "integration.rubi_4_3_2_1_r19"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.var "x")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.var "b") (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12831
  description := "RUBI 4.3.2.1 #19"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:19" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#19"


/-- RUBI 4.3.2.1 #50 -/
def rubi4321r50 : CRule where
  id := "integration.rubi_4_3_2_1_r50"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:50"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d"))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 12833
  description := "RUBI 4.3.2.1 #50"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:50" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#50"

/-- RUBI 4.3.4.2 #4 -/
def rubi4342r4 : CRule where
  id := "integration.rubi_4_3_4_2_r4"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "c")) (.var "d"))) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "d") (.int 2)) (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "d") (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.app2 .mul (.var "B") (.var "d")))) (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "c")) (.var "d"))) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2)))))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.var "c"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.var "C"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "A")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.var "d")))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12834
  description := "RUBI 4.3.4.2 #4"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):4" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#4"



























/-- RUBI 4.1.9 #2 -/
def rubi419r2 : CRule where
  id := "integration.rubi_4_1_9_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 12861
  description := "RUBI 4.1.9 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:2" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#2"

/-- RUBI 4.1.0.1 #1 -/
def rubi4101r1 : CRule where
  id := "integration.rubi_4_1_0_1_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2)) (.int 0),
    .ne (.var "m") (.int (-1))]
  priority := 12862
  description := "RUBI 4.1.0.1 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:1" "4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n.m#1"

/-- RUBI 4.1.0.1 #10 -/
def rubi4101r10 : CRule where
  id := "integration.rubi_4_1_0_1_r10"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.app2 .root (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.app2 .root (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.pow (.app2 .root (.app1 .sin (.app2 .add (.app2 .mul (.int 2) (.var "e")) (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "x")))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .root (.app1 .sin (.app2 .add (.app2 .mul (.int 2) (.var "e")) (.app2 .mul (.app2 .mul (.int 2) (.var "f")) (.var "x")))) (.int 2)))]
  independent := ["a", "b", "e", "f"]
  priority := 12863
  description := "RUBI 4.1.0.1 #10"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n:10" "4 Trig functions/4.1 Sine/4.1.0.1 (a sin)^m (b trg)^n.m#10"


/-- RUBI 4.1.1.2 #7 -/
def rubi4112r7 : CRule where
  id := "integration.rubi_4_1_1_2_r7"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:7"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1))))
  independent := ["a", "b", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))) (.int 0),
    .ne (.var "m") (.int 1)]
  priority := 12865
  description := "RUBI 4.1.1.2 #7"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:7" "4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.m#7"





/-- RUBI 4.1.4.2 #3 -/
def rubi4142r3 : CRule where
  id := "integration.rubi_4_1_4_2_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "b")) (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "d")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "c")) (.app2 .add (.var "m") (.int 2))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "m") (.int 1)))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")) (.var "d")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12870
  description := "RUBI 4.1.4.2 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):3" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#3"

/-- RUBI 4.1.4.2 #20 -/
def rubi4142r20 : CRule where
  id := "integration.rubi_4_1_4_2_r20"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "n") (.int 1))))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "n") (.int 1))))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12871
  description := "RUBI 4.1.4.2 #20"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):20" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#20"

/-- RUBI 4.1.4.2 #33 -/
def rubi4142r33 : CRule where
  id := "integration.rubi_4_1_4_2_r33"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.int 2) (.var "d")) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.int 3) (.pow (.int 2) (.int (-1))))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "A")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.var "a") (.var "B")))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "B")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 12872
  description := "RUBI 4.1.4.2 #33"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):33" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#33"

/-- RUBI 4.1.2.1 #2 -/
def rubi4121r2 : CRule where
  id := "integration.rubi_4_1_2_1_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "x")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 12873
  description := "RUBI 4.1.2.1 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:2" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#2"

/-- RUBI 4.1.2.1 #13 -/
def rubi4121r13 : CRule where
  id := "integration.rubi_4_1_2_1_r13"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "d") (.var "f")) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "d") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "d")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "d")))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 12874
  description := "RUBI 4.1.2.1 #13"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:13" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#13"

/-- RUBI 4.1.2.1 #19 -/
def rubi4121r19 : CRule where
  id := "integration.rubi_4_1_2_1_r19"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12875
  description := "RUBI 4.1.2.1 #19"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:19" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#19"

/-- RUBI 4.1.2.1 #27 -/
def rubi4121r27 : CRule where
  id := "integration.rubi_4_1_2_1_r27"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:27"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "d")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.var "b") (.app2 .add (.pow (.var "d") (.int 2)) (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 1)))))) (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "m") (.int 2))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12876
  description := "RUBI 4.1.2.1 #27"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:27" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#27"



/-- RUBI 4.1.10 #15 -/
def rubi4110r15 : CRule where
  id := "integration.rubi_4_1_10_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .mul (.pow (.var "f") (.int 2)) (.pow (.var "n") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "n")) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["b", "c", "d", "e", "f", "n"]
  conditions := [.gt (.var "n") (.int 1)]
  priority := 12879
  description := "RUBI 4.1.10 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:15" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#15"

/-- RUBI 4.1.10 #29 -/
def rubi4110r29 : CRule where
  id := "integration.rubi_4_1_10_r29"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "f") (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 12880
  description := "RUBI 4.1.10 #29"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:29" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#29"

/-- RUBI 4.1.3.1 #6 -/
def rubi4131r6 : CRule where
  id := "integration.rubi_4_1_3_1_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12881
  description := "RUBI 4.1.3.1 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):6" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#6"



/-- RUBI 4.1.5 #10 -/
def rubi415r10 : CRule where
  id := "integration.rubi_4_1_5_r10"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 12884
  description := "RUBI 4.1.5 #10"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:10" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#10"


/-- RUBI 4.1.5 #36 -/
def rubi415r36 : CRule where
  id := "integration.rubi_4_1_5_r36"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 2))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12886
  description := "RUBI 4.1.5 #36"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:36" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#36"

/-- RUBI 4.1.7 #5 -/
def rubi417r5 : CRule where
  id := "integration.rubi_4_1_7_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.var "p")) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "a") (.var "b"))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "a") (.var "b"))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B")))) (.app2 .add (.var "p") (.int 2))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "e", "f", "A", "B", "p"]
  conditions := [.gt (.int (-1)) (.var "p"),
    .ne (.app2 .add (.var "a") (.var "b")) (.int 0)]
  priority := 12887
  description := "RUBI 4.1.7 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:5" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#5"

/-- RUBI 4.1.2.2 #6 -/
def rubi4122r6 : CRule where
  id := "integration.rubi_4_1_2_2_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "d", "e", "f", "g", "n", "p"]
  priority := 12888
  description := "RUBI 4.1.2.2 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:6" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#6"


/-- RUBI 4.1.2.2 #28 -/
def rubi4122r28 : CRule where
  id := "integration.rubi_4_1_2_2_r28"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)))) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)]
  priority := 12890
  description := "RUBI 4.1.2.2 #28"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:28" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#28"

/-- RUBI 4.1.2.2 #35 -/
def rubi4122r35 : CRule where
  id := "integration.rubi_4_1_2_2_r35"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:35"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p"))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12891
  description := "RUBI 4.1.2.2 #35"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:35" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#35"

/-- RUBI 4.1.2.2 #46 -/
def rubi4122r46 : CRule where
  id := "integration.rubi_4_1_2_2_r46"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:46"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.var "g")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2)) (.int 0)]
  priority := 12892
  description := "RUBI 4.1.2.2 #46"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:46" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#46"




/-- RUBI 4.1.1.1 #6 -/
def rubi4111r6 : CRule where
  id := "integration.rubi_4_1_1_1_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:6"
  shape := .antideriv; x := "x"
  body := (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.var "d") (.int (-1))))
  independent := ["c", "d"]
  priority := 12896
  description := "RUBI 4.1.1.1 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:6" "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#6"

/-- RUBI 4.1.1.1 #15 -/
def rubi4111r15 : CRule where
  id := "integration.rubi_4_1_1_1_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:15"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.int (-1)) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "b") (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12897
  description := "RUBI 4.1.1.1 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:15" "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#15"

/-- RUBI 4.1.1.3 #1 -/
def rubi4113r1x : CRule where
  id := "integration.rubi_4_1_1_3_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "a") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "b") (.var "g")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .mul (.var "g") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")))),
    ("I2", (.app2 .mul (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .mul (.var "g") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))))]
  independent := ["a", "b", "e", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.var "p") (.int (-1))]
  priority := 12898
  description := "RUBI 4.1.1.3 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:1" "4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.m#1"

/-- RUBI 4.1.1.3 #24 -/
def rubi4113r24 : CRule where
  id := "integration.rubi_4_1_1_3_r24"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .mul (.var "g") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .root (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.app2 .root (.app2 .mul (.var "g") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.int 2))) (.pow (.app2 .root (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .mul (.app2 .root (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "g"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12899
  description := "RUBI 4.1.1.3 #24"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m:24" "4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.m#24"

/-- RUBI 4.1.4.1 #6 -/
def rubi4141r6 : CRule where
  id := "integration.rubi_4_1_4_1_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "B", "C", "m"]
  conditions := [.eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 12900
  description := "RUBI 4.1.4.1 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):6" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#6"

/-- RUBI 4.1.4.1 #13 -/
def rubi4141r13 : CRule where
  id := "integration.rubi_4_1_4_1_r13"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.var "A") (.var "C"))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "A") (.var "C"))) (.app2 .add (.var "m") (.int 1))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "C", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 12901
  description := "RUBI 4.1.4.1 #13"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):13" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#13"


/-- RUBI 4.1.0.2 #1 -/
def rubi4102r1 : CRule where
  id := "integration.rubi_4_1_0_2_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .mul (.var "a") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m"))) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.var "m")) (.int (-1))))
  independent := ["a", "b", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 12903
  description := "RUBI 4.1.0.2 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n:1" "4 Trig functions/4.1 Sine/4.1.0.2 (a trg)^m (b tan)^n.m#1"


/-- RUBI 4.1.6 #2 -/
def rubi416r2 : CRule where
  id := "integration.rubi_4_1_6_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:2"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "e") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .gt (.var "n") (.int 0)]
  priority := 12905
  description := "RUBI 4.1.6 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:2" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#2"

/-- RUBI 4.1.6 #9 -/
def rubi416r9 : CRule where
  id := "integration.rubi_4_1_6_r9"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:9"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "e") (.var "n")) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.var "n") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "n") (.pow (.var "a") (.int 2))) (.app2 .mul (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.app2 .mul (.int (-1)) (.int 1)))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 12906
  description := "RUBI 4.1.6 #9"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:9" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#9"

/-- RUBI 4.1.6 #20 -/
def rubi416r20 : CRule where
  id := "integration.rubi_4_1_6_r20"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:20"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "x")) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "B")) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "A", "B"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.int 0)]
  priority := 12907
  description := "RUBI 4.1.6 #20"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:20" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#20"

/-- RUBI 4.1.6 #25 -/
def rubi416r25 : CRule where
  id := "integration.rubi_4_1_6_r25"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:25"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "C", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 12908
  description := "RUBI 4.1.6 #25"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:25" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#25"

/-- RUBI 4.1.6 #30 -/
def rubi416r30 : CRule where
  id := "integration.rubi_4_1_6_r30"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:30"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.pow (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1))))
  independent := ["b", "c", "d", "e", "B", "C", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.int 0)]
  priority := 12909
  description := "RUBI 4.1.6 #30"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:30" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#30"

/-- RUBI 4.1.6 #35 -/
def rubi416r35 : CRule where
  id := "integration.rubi_4_1_6_r35"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:35"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A")))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A"))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.int 0)]
  priority := 12910
  description := "RUBI 4.1.6 #35"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:35" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#35"

/-- RUBI 4.1.6 #40 -/
def rubi416r40 : CRule where
  id := "integration.rubi_4_1_6_r40"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:40"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.var "c") (.var "A")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A"))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.pow (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.int 0)]
  priority := 12911
  description := "RUBI 4.1.6 #40"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:40" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#40"

/-- RUBI 4.7.4 #6 -/
def rubi474r6 : CRule where
  id := "integration.rubi_4_7_4_r6"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:6"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "e") (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "m")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "p")) (.pow (.pow (.var "e") (.var "p")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x")))) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "m", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2),
    .int (.var "p")]
  priority := 12912
  description := "RUBI 4.7.4 #6"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:6" "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#6"

/-- RUBI 4.7.4 #31 -/
def rubi474r31 : CRule where
  id := "integration.rubi_4_7_4_r31"; legacyId := some "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "e") (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "m")) (.pow (.app2 .mul (.var "f") (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.var "n"))) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "p")))
  result := (.app2 .mul (.app2 .mul (.pow (.int 2) (.var "p")) (.pow (.app2 .mul (.pow (.var "e") (.var "p")) (.pow (.var "f") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "e") (.app1 .cos (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "m") (.var "p"))) (.pow (.app2 .mul (.var "f") (.app1 .sin (.app2 .add (.var "a") (.app2 .mul (.var "b") (.var "x"))))) (.app2 .add (.var "n") (.var "p")))))]
  independent := ["a", "b", "c", "d", "e", "f", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.int 2),
    .int (.var "p")]
  priority := 12913
  description := "RUBI 4.7.4 #31"
  provenance := migrated "rubi:4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n:31" "4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m#31"


/-- RUBI 4.3.1.1 #6 -/
def rubi4311r6 : CRule where
  id := "integration.rubi_4_3_1_1_r6"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:6"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "n") (.int 1)]
  priority := 12915
  description := "RUBI 4.3.1.1 #6"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:6" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#6"



/-- RUBI 4.3.10 #5 -/
def rubi4310r5 : CRule where
  id := "integration.rubi_4_3_10_r5"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:5"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m"))) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.var "m")) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.var "m")) (.pow (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2))))))]
  independent := ["b", "c", "d", "e", "f", "m", "n"]
  conditions := [.gt (.var "n") (.int 1),
    .gt (.var "m") (.int 0)]
  priority := 12918
  description := "RUBI 4.3.10 #5"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n:5" "4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.m#5"


/-- RUBI 4.3.9 #19 -/
def rubi439r19 : CRule where
  id := "integration.rubi_4_3_9_r19"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p:19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n")]
  priority := 12920
  description := "RUBI 4.3.9 #19"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p:19" "4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p.m#19"

/-- RUBI 4.3.4.1 #13 -/
def rubi4341r13 : CRule where
  id := "integration.rubi_4_3_4_1_r13"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):13"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C")))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "C", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 12921
  description := "RUBI 4.3.4.1 #13"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):13" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#13"

/-- RUBI 4.3.2.1 #8 -/
def rubi4321r8 : CRule where
  id := "integration.rubi_4_3_2_1_r8"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 12922
  description := "RUBI 4.3.2.1 #8"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:8" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#8"


/-- RUBI 4.3.4.2 #1 -/
def rubi4342r1 : CRule where
  id := "integration.rubi_4_3_4_2_r1"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 12924
  description := "RUBI 4.3.4.2 #1"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):1" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#1"

/-- RUBI 4.3.4.2 #15 -/
def rubi4342r15 : CRule where
  id := "integration.rubi_4_3_4_2_r15"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))) (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C")))) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))))))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 12925
  description := "RUBI 4.3.4.2 #15"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):15" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#15"


























/-! ## Refutations -/

theorem rubi4122r22_counterexample_real : ¬ rubi4122r22.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4122r22.conditions rubi4122r22.body rubi4122r22.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "g" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4122r22, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4122r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4122r38_counterexample_real : ¬ rubi4122r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r38.conditions rubi4122r38.body rubi4122r38.result rubi4122r38.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4122r38, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4122r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4122r48_counterexample_real : ¬ rubi4122r48.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r48.conditions rubi4122r48.body rubi4122r48.result rubi4122r48.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r48, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r48, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r48.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r48, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r48, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r48, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4111r2_counterexample_real : ¬ rubi4111r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4111r2.conditions rubi4111r2.body rubi4111r2.result
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
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4111r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4111r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4111r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4111r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4111r11_counterexample_real : ¬ rubi4111r11.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4111r11.conditions rubi4111r11.body rubi4111r11.result
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
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4111r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4111r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4111r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4111r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4141r1_counterexample_real : ¬ rubi4141r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r1.conditions rubi4141r1.body rubi4141r1.result rubi4141r1.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4141r10_counterexample_real : ¬ rubi4141r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r10.conditions rubi4141r10.body rubi4141r10.result rubi4141r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then ((-1 : ℝ) / 2) else if s = "a" then (-3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then ((-1 : ℝ) / 2) else if s = "a" then (-3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r14_counterexample_real : ¬ rubi416r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r14.conditions rubi416r14.body rubi416r14.result rubi416r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r22_counterexample_real : ¬ rubi416r22.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r22.conditions rubi416r22.body rubi416r22.result rubi416r22.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then ((1 : ℝ) / 2) else if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r22.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then ((1 : ℝ) / 2) else if s = "b" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r22, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r22, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r27_counterexample_real : ¬ rubi416r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r27.conditions rubi416r27.body rubi416r27.result rubi416r27.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-1 : ℝ) else if s = "c" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-1 : ℝ) else if s = "c" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r32_counterexample_real : ¬ rubi416r32.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r32.conditions rubi416r32.body rubi416r32.result rubi416r32.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r32.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r32, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r32, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r37_counterexample_real : ¬ rubi416r37.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r37.conditions rubi416r37.body rubi416r37.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r37, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r37, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r42_counterexample_real : ¬ rubi416r42.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r42.conditions rubi416r42.body rubi416r42.result rubi416r42.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r42, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r42, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r42.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r42, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r42, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r42, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4331r23_counterexample_real : ¬ rubi4331r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4331r23.conditions rubi4331r23.body rubi4331r23.result rubi4331r23.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4331r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4331r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4331r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "m" then (1 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4331r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4331r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4331r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4311r1_counterexample_real : ¬ rubi4311r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4311r1.conditions rubi4311r1.body rubi4311r1.result rubi4311r1.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4311r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4311r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4311r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4311r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4311r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4311r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4311r10_counterexample_real : ¬ rubi4311r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4311r10.conditions rubi4311r10.body rubi4311r10.result rubi4311r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4311r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4311r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4311r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4311r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4311r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4311r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4312r25_counterexample_real : ¬ rubi4312r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4312r25.conditions rubi4312r25.body rubi4312r25.result rubi4312r25.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "m" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4312r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4312r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4312r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "m" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4312r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4312r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4312r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4341r3_counterexample_real : ¬ rubi4341r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4341r3.conditions rubi4341r3.body rubi4341r3.result rubi4341r3.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4341r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4341r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4341r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4341r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4341r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4341r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r4_counterexample_real : ¬ rubi4321r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r4.conditions rubi4321r4.body rubi4321r4.result rubi4321r4.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4321r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4321r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4321r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4321r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r19_counterexample_real : ¬ rubi4321r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r19.conditions rubi4321r19.body rubi4321r19.result rubi4321r19.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4321r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4321r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4321r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4321r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r50_counterexample_real : ¬ rubi4321r50.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r50.conditions rubi4321r50.body rubi4321r50.result rubi4321r50.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then (3 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4321r50, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4321r50, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4342r4_counterexample_real : ¬ rubi4342r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4342r4.conditions rubi4342r4.body rubi4342r4.result rubi4342r4.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "B" then ((1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4342r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4342r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4342r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "B" then ((1 : ℝ) / 2) else if s = "b" then ((1 : ℝ) / 2) else if s = "c" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4342r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4342r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4342r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi419r2_counterexample_real : ¬ rubi419r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r2.conditions rubi419r2.body rubi419r2.result rubi419r2.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4101r1_counterexample_real : ¬ rubi4101r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4101r1.conditions rubi4101r1.body rubi4101r1.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4101r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4101r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4101r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4101r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4101r10_counterexample_real : ¬ rubi4101r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4101r10.conditions rubi4101r10.body rubi4101r10.result rubi4101r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4101r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4101r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4101r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4101r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4101r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4101r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4112r7_counterexample_real : ¬ rubi4112r7.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4112r7.conditions rubi4112r7.body rubi4112r7.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "e" then (-3 : ℝ) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4112r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4112r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4112r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4112r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4142r3_counterexample_real : ¬ rubi4142r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r3.conditions rubi4142r3.body rubi4142r3.result rubi4142r3.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "d" then (2 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "d" then (2 : ℝ) else if s = "f" then (-1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r20_counterexample_real : ¬ rubi4142r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r20.conditions rubi4142r20.body rubi4142r20.result rubi4142r20.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (-1 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (-1 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r20, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r33_counterexample_real : ¬ rubi4142r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r33.conditions rubi4142r33.body rubi4142r33.result rubi4142r33.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "d" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "d" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r33, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r2_counterexample_real : ¬ rubi4121r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r2.conditions rubi4121r2.body rubi4121r2.result rubi4121r2.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r13_counterexample_real : ¬ rubi4121r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r13.conditions rubi4121r13.body rubi4121r13.result rubi4121r13.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "c" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r19_counterexample_real : ¬ rubi4121r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r19.conditions rubi4121r19.body rubi4121r19.result rubi4121r19.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r27_counterexample_real : ¬ rubi4121r27.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r27.conditions rubi4121r27.body rubi4121r27.result rubi4121r27.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "c" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r27.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "c" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r27, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r27, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r15_counterexample_real : ¬ rubi4110r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r15.conditions rubi4110r15.body rubi4110r15.result rubi4110r15.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r29_counterexample_real : ¬ rubi4110r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r29.conditions rubi4110r29.body rubi4110r29.result rubi4110r29.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4110r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4110r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4110r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4110r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4131r6_counterexample_real : ¬ rubi4131r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4131r6.conditions rubi4131r6.body rubi4131r6.result rubi4131r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4131r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4131r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4131r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4131r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r10_counterexample_real : ¬ rubi415r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r10.conditions rubi415r10.body rubi415r10.result rubi415r10.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r10.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (-3 : ℝ) else if s = "n" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r36_counterexample_real : ¬ rubi415r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r36.conditions rubi415r36.body rubi415r36.result rubi415r36.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r36.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r36, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r5_counterexample_real : ¬ rubi417r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r5.conditions rubi417r5.body rubi417r5.result rubi417r5.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "p" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r6_counterexample_real : ¬ rubi4122r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r6.conditions rubi4122r6.body rubi4122r6.result rubi4122r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r28_counterexample_real : ¬ rubi4122r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r28.conditions rubi4122r28.body rubi4122r28.result rubi4122r28.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "g" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "g" then (-1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r28, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r35_counterexample_real : ¬ rubi4122r35.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r35.conditions rubi4122r35.body rubi4122r35.result rubi4122r35.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (2 : ℝ) else if s = "e" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r35.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (2 : ℝ) else if s = "e" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r35, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r46_counterexample_real : ¬ rubi4122r46.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r46.conditions rubi4122r46.body rubi4122r46.result rubi4122r46.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r46, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r46, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r46.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r46, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r46, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r46, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4111r6_counterexample_real : ¬ rubi4111r6.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4111r6.conditions rubi4111r6.body rubi4111r6.result
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
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4111r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4111r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4111r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4111r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4111r15_counterexample_real : ¬ rubi4111r15.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4111r15.conditions rubi4111r15.body rubi4111r15.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-3 : ℝ) else if s = "b" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4111r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4111r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4111r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4111r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4113r1x_counterexample_real : ¬ rubi4113r1x.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r1x.conditions rubi4113r1x.body rubi4113r1x.result rubi4113r1x.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4113r1x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4113r1x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4113r1x.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4113r1x, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4113r1x, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4113r1x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4113r24_counterexample_real : ¬ rubi4113r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4113r24.conditions rubi4113r24.body rubi4113r24.result rubi4113r24.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4113r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4113r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4113r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4113r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4113r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4113r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4141r6_counterexample_real : ¬ rubi4141r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r6.conditions rubi4141r6.body rubi4141r6.result rubi4141r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4141r13_counterexample_real : ¬ rubi4141r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r13.conditions rubi4141r13.body rubi4141r13.result rubi4141r13.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4102r1_counterexample_real : ¬ rubi4102r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4102r1.conditions rubi4102r1.body rubi4102r1.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "m" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4102r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4102r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4102r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4102r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r2_counterexample_real : ¬ rubi416r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r2.conditions rubi416r2.body rubi416r2.result rubi416r2.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r9_counterexample_real : ¬ rubi416r9.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r9.conditions rubi416r9.body rubi416r9.result rubi416r9.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r9.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (1 : ℝ) else if s = "n" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r9, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r20_counterexample_real : ¬ rubi416r20.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r20.conditions rubi416r20.body rubi416r20.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r20, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r25_counterexample_real : ¬ rubi416r25.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r25.conditions rubi416r25.body rubi416r25.result
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
  refine not_antiderivHoldsUnder (fun s => 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r30_counterexample_real : ¬ rubi416r30.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r30.conditions rubi416r30.body rubi416r30.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "b" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r30, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r35_counterexample_real : ¬ rubi416r35.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r35.conditions rubi416r35.body rubi416r35.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "b" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r35, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r35, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r40_counterexample_real : ¬ rubi416r40.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r40.conditions rubi416r40.body rubi416r40.result rubi416r40.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (1 : ℝ) else if s = "a" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r40.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (1 : ℝ) else if s = "a" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r40, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r40, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r40, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi474r6_counterexample_real : ¬ rubi474r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi474r6.conditions rubi474r6.body rubi474r6.result rubi474r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi474r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi474r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi474r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "p" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi474r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi474r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi474r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi474r31_counterexample_real : ¬ rubi474r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi474r31.conditions rubi474r31.body rubi474r31.result rubi474r31.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "n" then (3 : ℝ) else if s = "p" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi474r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi474r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi474r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else if s = "n" then (3 : ℝ) else if s = "p" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi474r31, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi474r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi474r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4311r6_counterexample_real : ¬ rubi4311r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4311r6.conditions rubi4311r6.body rubi4311r6.result rubi4311r6.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4311r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4311r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4311r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4311r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4311r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4311r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4310r5_counterexample_real : ¬ rubi4310r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4310r5.conditions rubi4310r5.body rubi4310r5.result rubi4310r5.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4310r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4310r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4310r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (2 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4310r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4310r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4310r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi439r19_counterexample_real : ¬ rubi439r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi439r19.conditions rubi439r19.body rubi439r19.result rubi439r19.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi439r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi439r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi439r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi439r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi439r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi439r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4341r13_counterexample_real : ¬ rubi4341r13.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4341r13.conditions rubi4341r13.body rubi4341r13.result rubi4341r13.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "C" then ((-1 : ℝ) / 2) else if s = "a" then (2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4341r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4341r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4341r13.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "C" then ((-1 : ℝ) / 2) else if s = "a" then (2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4341r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4341r13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4341r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r8_counterexample_real : ¬ rubi4321r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r8.conditions rubi4321r8.body rubi4321r8.result rubi4321r8.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4321r8.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4321r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4321r8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4321r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4342r1_counterexample_real : ¬ rubi4342r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4342r1.conditions rubi4342r1.body rubi4342r1.result rubi4342r1.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then ((-1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4342r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4342r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4342r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then ((-1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4342r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4342r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4342r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4342r15_counterexample_real : ¬ rubi4342r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4342r15.conditions rubi4342r15.body rubi4342r15.result rubi4342r15.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (-1 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4342r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4342r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4342r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (-1 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4342r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4342r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4342r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

end OSR.IntegrationRec174
