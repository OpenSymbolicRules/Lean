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

namespace OSR.IntegrationRec175

open OSR OSR.Calculus Filter Topology

private def repo : String := "OpenSymbolicRules/Integration"
private def rev : String := "f84ed2a81702836c019e647e0a586b8d576ae7c6"

private def migrated (legacy rubi : String) : Provenance :=
  { method := .derived,
    sources := [
      { name := repo, locator := legacy, revision := some rev, license := some "MIT" },
      { name := "Rubi", locator := rubi, revision := some "4.16.1", license := some "MIT" }] }

/-! ## Rules -/





/-- RUBI 4.1.9 #29 -/
def rubi419r29 : CRule where
  id := "integration.rubi_4_1_9_r29"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n")]
  priority := 13004
  description := "RUBI 4.1.9 #29"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:29" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#29"






/-- RUBI 4.1.1.2 #33 -/
def rubi4112r33x : CRule where
  id := "integration.rubi_4_1_1_2_r33"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.var "a") (.app2 .mul (.int (-1)) (.var "b")))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .mul (.pow (.var "g") (.int 2)) (.app2 .add (.var "a") (.app2 .mul (.int (-1)) (.var "b")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.int 1) (.app2 .mul (.int (-1)) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2)) (.int 0)]
  priority := 13010
  description := "RUBI 4.1.1.2 #33"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m:33" "4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.m#33"


/-- RUBI 4.1.4.2 #1 -/
def rubi4142r1 : CRule where
  id := "integration.rubi_4_1_4_2_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):1"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C"))) (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 13012
  description := "RUBI 4.1.4.2 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):1" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#1"

/-- RUBI 4.1.4.2 #14 -/
def rubi4142r14 : CRule where
  id := "integration.rubi_4_1_4_2_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.app2 .add (.var "A") (.var "C"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "n")) (.int 2))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.app2 .mul (.int (-1)) (.int 1))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C", "n", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")]
  priority := 13013
  description := "RUBI 4.1.4.2 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):14" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#14"

/-- RUBI 4.1.4.2 #31 -/
def rubi4142r31 : CRule where
  id := "integration.rubi_4_1_4_2_r31"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):31"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "C") (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))),
    ("I2", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "b")) (.var "d"))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.var "d"))) (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.var "d"))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 13014
  description := "RUBI 4.1.4.2 #31"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):31" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#31"

/-- RUBI 4.1.4.2 #36 -/
def rubi4142r36 : CRule where
  id := "integration.rubi_4_1_4_2_r36"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):36"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.var "C") (.pow (.app2 .mul (.var "b") (.var "d")) (.int (-1)))) (.var "I2"))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I3")))
  integrals := [("I1", (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))),
    ("I2", (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1)))),
    ("I3", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "d", "e", "f", "A", "C", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13015
  description := "RUBI 4.1.4.2 #36"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):36" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#36"

/-- RUBI 4.1.2.1 #16 -/
def rubi4121r16 : CRule where
  id := "integration.rubi_4_1_2_1_r16"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:16"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "m") (.int 1)))) (.int 0)]
  priority := 13016
  description := "RUBI 4.1.2.1 #16"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:16" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#16"

/-- RUBI 4.1.2.1 #23 -/
def rubi4121r23 : CRule where
  id := "integration.rubi_4_1_2_1_r23"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))),
    ("I2", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13017
  description := "RUBI 4.1.2.1 #23"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:23" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#23"

/-- RUBI 4.1.2.1 #44 -/
def rubi4121r44 : CRule where
  id := "integration.rubi_4_1_2_1_r44"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:44"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0)]
  priority := 13018
  description := "RUBI 4.1.2.1 #44"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:44" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#44"

/-- RUBI 4.1.2.1 #56 -/
def rubi4121r56 : CRule where
  id := "integration.rubi_4_1_2_1_r56"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:56"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.var "d")) (.pow (.var "b") (.int (-1)))) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1)))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.pow (.var "d") (.int 2)) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["b", "c", "d", "e", "f", "m"]
  priority := 13019
  description := "RUBI 4.1.2.1 #56"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:56" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#56"

/-- RUBI 4.1.2.1 #89 -/
def rubi4121r89 : CRule where
  id := "integration.rubi_4_1_2_1_r89"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:89"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.var "d") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))))]
  independent := ["a", "b", "c", "d", "e", "f", "n", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .int (.var "m"),
    .gt (.var "m") (.int 0)]
  priority := 13020
  description := "RUBI 4.1.2.1 #89"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:89" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#89"

/-- RUBI 4.1.10 #8 -/
def rubi4110r8 : CRule where
  id := "integration.rubi_4_1_10_r8"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:8"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app1 .cos (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1))))) (.var "I1")) (.app2 .mul (.app1 .sin (.app2 .mul (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.pow (.var "d") (.int (-1))))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app1 .sin (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1))))),
    ("I2", (.app2 .mul (.app1 .cos (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "f")) (.pow (.var "d") (.int (-1)))) (.app2 .mul (.var "f") (.var "x")))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))) (.int (-1)))))]
  independent := ["c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "d") (.var "e")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "f"))) (.int 0)]
  priority := 13021
  description := "RUBI 4.1.10 #8"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n:8" "4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m#8"


/-- RUBI 4.1.3.1 #15 -/
def rubi4131r15 : CRule where
  id := "integration.rubi_4_1_3_1_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 3))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13023
  description := "RUBI 4.1.3.1 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):15" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#15"


/-- RUBI 4.1.5 #6 -/
def rubi415r6 : CRule where
  id := "integration.rubi_4_1_5_r6"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:6"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.var "n") (.int 2)) (.pow (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 2))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n"),
    .ne (.var "n") (.int (-2))]
  priority := 13025
  description := "RUBI 4.1.5 #6"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:6" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#6"

/-- RUBI 4.1.5 #15 -/
def rubi415r15 : CRule where
  id := "integration.rubi_4_1_5_r15"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:15"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))
  result := (.var "I1")
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.var "a") (.app1 .cot (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")))]
  independent := ["a", "b", "c", "d", "m", "n"]
  conditions := [.eq (.app2 .add (.var "m") (.var "n")) (.int 0),
    .int (.var "n"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 13026
  description := "RUBI 4.1.5 #15"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:15" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#15"

/-- RUBI 4.1.5 #24 -/
def rubi415r24 : CRule where
  id := "integration.rubi_4_1_5_r24"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n")) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.var "d") (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.var "a") (.var "I1"))) (.app2 .mul (.pow (.var "b") (.int 2)) (.var "I2")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13027
  description := "RUBI 4.1.5 #24"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:24" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#24"

/-- RUBI 4.1.5 #29 -/
def rubi415r29 : CRule where
  id := "integration.rubi_4_1_5_r29"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 13028
  description := "RUBI 4.1.5 #29"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:29" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#29"

/-- RUBI 4.1.5 #34 -/
def rubi415r34 : CRule where
  id := "integration.rubi_4_1_5_r34"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "m") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.int 1)))),
    ("I2", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.int 2))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 13029
  description := "RUBI 4.1.5 #34"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:34" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#34"

/-- RUBI 4.1.7 #3 -/
def rubi417r3 : CRule where
  id := "integration.rubi_4_1_7_r3"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:3"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.var "x")) (.pow (.var "b") (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.var "b") (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B"]
  priority := 13030
  description := "RUBI 4.1.7 #3"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:3" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#3"

/-- RUBI 4.1.7 #14 -/
def rubi417r14 : CRule where
  id := "integration.rubi_4_1_7_r14"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:14"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.var "p"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "f")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "a") (.var "b"))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.var "a") (.var "b"))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.app2 .add (.var "p") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.app2 .add (.var "p") (.int 1))) (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.int 2) (.var "p")) (.int 3)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "b")) (.app2 .add (.var "p") (.int 2))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "e", "f", "p"]
  conditions := [.ne (.app2 .add (.var "a") (.var "b")) (.int 0),
    .gt (.int (-1)) (.var "p")]
  priority := 13031
  description := "RUBI 4.1.7 #14"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:14" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#14"

/-- RUBI 4.1.2.2 #10 -/
def rubi4122r10 : CRule where
  id := "integration.rubi_4_1_2_2_r10"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:10"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13032
  description := "RUBI 4.1.2.2 #10"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:10" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#10"


/-- RUBI 4.1.2.2 #33 -/
def rubi4122r33 : CRule where
  id := "integration.rubi_4_1_2_2_r33"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "g") (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")) (.var "p"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "m") (.var "p"))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.var "g") (.int 2)) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.var "m") (.var "p"))) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "c")) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.var "p")) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app2 .add (.var "m") (.var "p")))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.var "p") (.int 1),
    .ne (.app2 .add (.var "m") (.var "p")) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0),
    .int (.app2 .mul (.int 2) (.var "m"))]
  priority := 13034
  description := "RUBI 4.1.2.2 #33"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:33" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#33"

/-- RUBI 4.1.2.2 #39 -/
def rubi4122r39 : CRule where
  id := "integration.rubi_4_1_2_2_r39"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.var "g")) (.var "m")) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.pow (.var "g") (.int 2)) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))))]
  independent := ["a", "b", "e", "f", "g", "m", "p"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 1)) (.int 0)]
  priority := 13035
  description := "RUBI 4.1.2.2 #39"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:39" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#39"



/-- RUBI 4.1.1.1 #13 -/
def rubi4111r13 : CRule where
  id := "integration.rubi_4_1_1_1_r13"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:13"
  shape := .antideriv; x := "x"
  body := (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-2)) (.var "b")) (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.app2 .mul (.var "d") (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13038
  description := "RUBI 4.1.1.1 #13"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n:13" "4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m#13"



/-- RUBI 4.1.4.1 #2 -/
def rubi4141r2 : CRule where
  id := "integration.rubi_4_1_4_1_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):2"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.var "A") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.int (-1))))
  independent := ["b", "e", "f", "A", "C", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.var "m") (.int 2))) (.app2 .mul (.var "C") (.app2 .add (.var "m") (.int 1)))) (.int 0)]
  priority := 13041
  description := "RUBI 4.1.4.1 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):2" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#2"

/-- RUBI 4.1.4.1 #11 -/
def rubi4141r11 : CRule where
  id := "integration.rubi_4_1_4_1_r11"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):11"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "A") (.var "C"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C")) (.var "m"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "C")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "C", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13042
  description := "RUBI 4.1.4.1 #11"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):11" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#11"




/-- RUBI 4.1.6 #5 -/
def rubi416r5 : CRule where
  id := "integration.rubi_4_1_6_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.pow (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.int 2) (.var "n")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "n"]
  conditions := [.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13046
  description := "RUBI 4.1.6 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:5" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#5"

/-- RUBI 4.1.6 #18 -/
def rubi416r18 : CRule where
  id := "integration.rubi_4_1_6_r18"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:18"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "x")) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))))) (.int 0)]
  priority := 13047
  description := "RUBI 4.1.6 #18"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:18" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#18"

/-- RUBI 4.1.6 #23 -/
def rubi416r23 : CRule where
  id := "integration.rubi_4_1_6_r23"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:23"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "B")) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.int 0)]
  priority := 13048
  description := "RUBI 4.1.6 #23"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:23" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#23"

/-- RUBI 4.1.6 #28 -/
def rubi416r28 : CRule where
  id := "integration.rubi_4_1_6_r28"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:28"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .mul (.var "a") (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))]
  independent := ["a", "b", "c", "d", "e", "A", "C", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 13049
  description := "RUBI 4.1.6 #28"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:28" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#28"

/-- RUBI 4.1.6 #33 -/
def rubi416r33 : CRule where
  id := "integration.rubi_4_1_6_r33"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:33"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.pow (.var "a") (.int 2)) (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))) (.var "B")) (.var "n"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.gt (.var "n") (.int 0),
    .ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)]
  priority := 13050
  description := "RUBI 4.1.6 #33"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:33" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#33"

/-- RUBI 4.1.6 #38 -/
def rubi416r38 : CRule where
  id := "integration.rubi_4_1_6_r38"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:38"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A")))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A"))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.pow (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "C"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.int 0)]
  priority := 13051
  description := "RUBI 4.1.6 #38"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:38" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#38"

/-- RUBI 4.1.6 #43 -/
def rubi416r43 : CRule where
  id := "integration.rubi_4_1_6_r43"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:43"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.var "B")) (.app2 .mul (.app2 .mul (.var "c") (.var "A")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A"))) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.var "n") (.int 1)) (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")))) (.app2 .mul (.app2 .mul (.app2 .add (.var "n") (.int 2)) (.app2 .add (.app2 .mul (.var "a") (.var "B")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "A")))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.var "n") (.int 2))) (.var "c")) (.var "A")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.gt (.int (-1)) (.var "n"),
    .ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.var "n") (.int (-2))]
  priority := 13052
  description := "RUBI 4.1.6 #43"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:43" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#43"





/-- RUBI 4.3.1.1 #11 -/
def rubi4311r11 : CRule where
  id := "integration.rubi_4_3_1_1_r11"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:11"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.var "n"))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))))]
  independent := ["a", "b", "c", "d", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13057
  description := "RUBI 4.3.1.1 #11"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:11" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#11"



/-- RUBI 4.3.4.1 #4 -/
def rubi4341r4 : CRule where
  id := "integration.rubi_4_3_4_1_r4"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "C", "m"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 13060
  description := "RUBI 4.3.4.1 #4"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):4" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#4"

/-- RUBI 4.3.2.1 #20 -/
def rubi4321r20 : CRule where
  id := "integration.rubi_4_3_2_1_r20"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.pow (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.pow (.var "c") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "d"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.pow (.var "d") (.int 2)))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.pow (.var "c") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "c")) (.var "d"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "d") (.int 2))))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 13061
  description := "RUBI 4.3.2.1 #20"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:20" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#20"

































/-- RUBI 4.1.9 #1 -/
def rubi419r1 : CRule where
  id := "integration.rubi_4_1_9_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 13094
  description := "RUBI 4.1.9 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:1" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#1"

/-- RUBI 4.1.9 #30 -/
def rubi419r30 : CRule where
  id := "integration.rubi_4_1_9_r30"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.pow (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.int 2)))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "n")) (.pow (.var "c") (.var "n"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.int 2) (.var "n")))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "n")]
  priority := 13095
  description := "RUBI 4.1.9 #30"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p:30" "4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m#30"







/-- RUBI 4.1.4.2 #2 -/
def rubi4142r2 : CRule where
  id := "integration.rubi_4_1_4_2_r2"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):2"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.pow (.pow (.var "b") (.int 2)) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0)]
  priority := 13102
  description := "RUBI 4.1.4.2 #2"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):2" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#2"

/-- RUBI 4.1.4.2 #19 -/
def rubi4142r19 : CRule where
  id := "integration.rubi_4_1_4_2_r19"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):19"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "C")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "c")) (.var "d"))) (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "d"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.app2 .add (.var "n") (.int 2))))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "n") (.int 1))))))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "n") (.int 1))))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13103
  description := "RUBI 4.1.4.2 #19"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2):19" "4 Trig functions/4.1 Sine/4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2).m#19"


/-- RUBI 4.1.2.1 #1 -/
def rubi4121r1 : CRule where
  id := "integration.rubi_4_1_2_1_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "c")) (.app2 .mul (.var "b") (.var "d"))) (.var "x")) (.pow (.int 2) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.var "f") (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .mul (.int 2) (.var "f")) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "f"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0)]
  priority := 13105
  description := "RUBI 4.1.2.1 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:1" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#1"

/-- RUBI 4.1.2.1 #9 -/
def rubi4121r9 : CRule where
  id := "integration.rubi_4_1_2_1_r9"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:9"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1)) (.int 0),
    .ne (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))]
  priority := 13106
  description := "RUBI 4.1.2.1 #9"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:9" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#9"

/-- RUBI 4.1.2.1 #17 -/
def rubi4121r17 : CRule where
  id := "integration.rubi_4_1_2_1_r17"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:17"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")]
  priority := 13107
  description := "RUBI 4.1.2.1 #17"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:17" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#17"

/-- RUBI 4.1.2.1 #25 -/
def rubi4121r25 : CRule where
  id := "integration.rubi_4_1_2_1_r25"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.var "a") (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 1))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "m"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1)))) (.var "m")]
  priority := 13108
  description := "RUBI 4.1.2.1 #25"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:25" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#25"


/-- RUBI 4.1.2.1 #57 -/
def rubi4121r57 : CRule where
  id := "integration.rubi_4_1_2_1_r57"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:57"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.var "c")) (.var "d"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "b")) (.var "c")) (.var "d")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))))) (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.pow (.var "d") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.var "a")) (.var "b")) (.var "c")) (.var "d")) (.app2 .add (.var "m") (.int 2)))) (.app2 .mul (.pow (.var "b") (.int 2)) (.app2 .add (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.pow (.var "c") (.int 2)) (.app2 .add (.var "m") (.int 2)))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "m")]
  priority := 13110
  description := "RUBI 4.1.2.1 #57"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:57" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#57"

/-- RUBI 4.1.2.1 #90 -/
def rubi4121r90 : CRule where
  id := "integration.rubi_4_1_2_1_r90"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:90"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.var "a") (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.pow (.var "d") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n")) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int (-1))))),
    ("I2", (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int (-1)))))]
  independent := ["a", "b", "d", "e", "f", "n"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13111
  description := "RUBI 4.1.2.1 #90"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n:90" "4 Trig functions/4.1 Sine/4.1.2.1 (a+b sin)^m (c+d sin)^n.m#90"


/-- RUBI 4.1.3.1 #5 -/
def rubi4131r5 : CRule where
  id := "integration.rubi_4_1_3_1_r5"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):5"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.var "f") (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m", "n"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))))) (.int 0),
    .ne (.var "m") (.app2 .mul (.int (-1)) (.pow (.int 2) (.int (-1))))]
  priority := 13113
  description := "RUBI 4.1.3.1 #5"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):5" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#5"

/-- RUBI 4.1.3.1 #24 -/
def rubi4131r24 : CRule where
  id := "integration.rubi_4_1_3_1_r24"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):24"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.var "c")) (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "c"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.var "a") (.var "B")))) (.var "d")))) (.app2 .add (.var "n") (.int 1)))) (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app2 .mul (.var "a") (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "c")) (.var "d")) (.app2 .mul (.var "B") (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.app2 .mul (.int (-1)) (.int 2)) (.pow (.var "d") (.int 2))))))))) (.app2 .add (.var "n") (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app2 .add (.var "n") (.int 2)))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "b")) (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.var "c"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "A")) (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B")) (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.app2 .mul (.pow (.var "d") (.int 2)) (.app2 .add (.var "n") (.int 1))))))) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2)))) (.int 0),
    .gt (.var "m") (.int 1),
    .gt (.int (-1)) (.var "n")]
  priority := 13114
  description := "RUBI 4.1.3.1 #24"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin):24" "4 Trig functions/4.1 Sine/4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin).m#24"



/-- RUBI 4.1.5 #30 -/
def rubi415r30 : CRule where
  id := "integration.rubi_4_1_5_r30"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:30"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.var "m")) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.var "a") (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1"))) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))),
    ("I2", (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 2)))) (.pow (.app2 .add (.app2 .mul (.var "a") (.app1 .cos (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "m"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "m") (.int 1)]
  priority := 13117
  description := "RUBI 4.1.5 #30"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n:30" "4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m#30"


/-- RUBI 4.1.7 #4 -/
def rubi417r4 : CRule where
  id := "integration.rubi_4_1_7_r4"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:4"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int 2))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "e", "f", "A", "B"]
  priority := 13119
  description := "RUBI 4.1.7 #4"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p:4" "4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m#4"

/-- RUBI 4.1.2.2 #12 -/
def rubi4122r12 : CRule where
  id := "integration.rubi_4_1_2_2_r12"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:12"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1)))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1))))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.app2 .mul (.int (-1)) (.int 1)))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "n", "p"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.int 0),
    .eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.var "p")) (.app2 .mul (.int (-1)) (.int 1))) (.int 0),
    .ne (.app2 .add (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.var "n"))) (.app2 .mul (.int (-1)) (.int 1))) (.int 0)]
  priority := 13120
  description := "RUBI 4.1.2.2 #12"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:12" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#12"

/-- RUBI 4.1.2.2 #25 -/
def rubi4122r25 : CRule where
  id := "integration.rubi_4_1_2_2_r25"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.var "f")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.var "b") (.int 3)) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 2))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "d")) (.app2 .add (.var "m") (.int 1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")) (.app2 .add (.app2 .mul (.int 2) (.var "m")) (.int 3))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.app2 .mul (.int (-3)) (.pow (.int 2) (.int (-1)))) (.var "m")]
  priority := 13121
  description := "RUBI 4.1.2.2 #25"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:25" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#25"

/-- RUBI 4.1.2.2 #34 -/
def rubi4122r34 : CRule where
  id := "integration.rubi_4_1_2_2_r34"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 1))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "f") (.var "g")) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.pow (.var "g") (.int 2)) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.app2 .add (.var "p") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "p") (.int 2))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.app2 .add (.app2 .add (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.pow (.var "a") (.int 2)) (.app2 .add (.var "p") (.int 2))) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 2))))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "a") (.var "b")) (.var "d")) (.var "m"))) (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.var "p")) (.int 3))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "g", "m", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0),
    .gt (.int (-1)) (.var "p"),
    .int (.app2 .mul (.int 2) (.var "m"))]
  priority := 13122
  description := "RUBI 4.1.2.2 #34"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:34" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#34"


/-- RUBI 4.1.2.2 #78 -/
def rubi4122r78 : CRule where
  id := "integration.rubi_4_1_2_2_r78"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:78"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.pow (.var "d") (.int (-1)))) (.var "I1")) (.var "I2"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.app2 .add (.var "n") (.int 1))))),
    ("I2", (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "g") (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "p")) (.pow (.app2 .mul (.var "d") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "n"))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.pow (.var "b") (.int 2)) (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "d", "e", "f", "g", "n", "p"]
  conditions := [.ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13124
  description := "RUBI 4.1.2.2 #78"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n:78" "4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m#78"




/-- RUBI 4.1.4.1 #12 -/
def rubi4141r12 : CRule where
  id := "integration.rubi_4_1_4_1_r12"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C")))) (.app1 .cos (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2))))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "B"))) (.app2 .mul (.var "a") (.var "C")))) (.app2 .add (.var "m") (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.app2 .mul (.app2 .mul (.var "b") (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.var "b") (.var "C")))) (.app2 .add (.var "m") (.int 1))))) (.app1 .sin (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "B", "C", "m"]
  conditions := [.gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.int 0)]
  priority := 13128
  description := "RUBI 4.1.4.1 #12"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2):12" "4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m#12"




/-- RUBI 4.1.6 #1 -/
def rubi416r1 : CRule where
  id := "integration.rubi_4_1_6_r1"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:1"
  shape := .antideriv; x := "x"
  body := (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2))
  result := (.app2 .mul (.app2 .mul (.int (-2)) (.app2 .add (.app2 .mul (.var "c") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .mul (.var "e") (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e"]
  conditions := [.eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0)]
  priority := 13132
  description := "RUBI 4.1.6 #1"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:1" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#1"


/-- RUBI 4.1.6 #19 -/
def rubi416r19 : CRule where
  id := "integration.rubi_4_1_6_r19"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:19"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.var "c") (.var "C")) (.var "x")) (.pow (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")) (.app1 .ln (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))))) (.pow (.app2 .mul (.var "e") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.int (-1)))))
  independent := ["a", "b", "c", "d", "e", "A", "C"]
  conditions := [.ne (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.pow (.var "b") (.int 2)) (.pow (.var "c") (.int 2)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.var "C"))) (.int 0)]
  priority := 13134
  description := "RUBI 4.1.6 #19"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:19" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#19"

/-- RUBI 4.1.6 #24 -/
def rubi416r24 : CRule where
  id := "integration.rubi_4_1_6_r24"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:24"
  shape := .antideriv; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "C")) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1))))
  independent := ["a", "b", "c", "d", "e", "A", "B", "C", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .eq (.app2 .add (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "c") (.var "C"))) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 13135
  description := "RUBI 4.1.6 #24"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:24" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#24"

/-- RUBI 4.1.6 #29 -/
def rubi416r29 : CRule where
  id := "integration.rubi_4_1_6_r29"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:29"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.var "a") (.var "B")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n"))) (.pow (.app2 .mul (.app2 .mul (.var "a") (.var "e")) (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.var "a") (.app2 .add (.var "n") (.int 1))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.var "n")))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "n"]
  conditions := [.ne (.var "n") (.int (-1)),
    .eq (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "B")) (.var "n")) (.app2 .mul (.app2 .mul (.var "a") (.var "A")) (.app2 .add (.var "n") (.int 1)))) (.int 0)]
  priority := 13136
  description := "RUBI 4.1.6 #29"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:29" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#29"

/-- RUBI 4.1.6 #34 -/
def rubi416r34 : CRule where
  id := "integration.rubi_4_1_6_r34"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:34"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "B") (.pow (.var "b") (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.pow (.var "b") (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2))),
    ("I2", (.app2 .mul (.int 1) (.pow (.app2 .root (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "B", "C"]
  conditions := [.eq (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C"))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.int 0)]
  priority := 13137
  description := "RUBI 4.1.6 #34"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:34" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#34"

/-- RUBI 4.1.6 #39 -/
def rubi416r39 : CRule where
  id := "integration.rubi_4_1_6_r39"; legacyId := some "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:39"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.var "C") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.pow (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int 2)) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "C")) (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "A"))) (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.app2 .mul (.var "b") (.var "A")) (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.pow (.app2 .mul (.app2 .mul (.var "e") (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2))))) (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x"))))))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.pow (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.int 1) (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .cos (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.app2 .mul (.var "c") (.app1 .sin (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "A", "C"]
  conditions := [.ne (.app2 .add (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.app2 .mul (.int (-1)) (.pow (.var "c") (.int 2)))) (.int 0),
    .ne (.app2 .add (.app2 .mul (.var "a") (.var "A")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "c")) (.var "C"))) (.int 0)]
  priority := 13138
  description := "RUBI 4.1.6 #39"
  provenance := migrated "rubi:4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n:39" "4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m#39"


/-- RUBI 4.3.3.1 #25 -/
def rubi4331r25 : CRule where
  id := "integration.rubi_4_3_3_1_r25"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):25"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int (-1))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .add (.app2 .mul (.var "B") (.var "a")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "b")))) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I2")))
  integrals := [("I1", (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d")))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .mul (.var "A") (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d")))))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.pow (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2)) (.int (-1))))),
    ("I2", (.app2 .mul (.app2 .add (.int 1) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))) (.pow (.app2 .mul (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .root (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.int 2))) (.int (-1)))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0)]
  priority := 13140
  description := "RUBI 4.3.3.1 #25"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan):25" "4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m#25"

/-- RUBI 4.3.1.1 #5 -/
def rubi4311r5 : CRule where
  id := "integration.rubi_4_3_1_1_r5"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:5"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))) (.int 2))
  result := (.app2 .add (.app2 .add (.app2 .mul (.app2 .add (.pow (.var "a") (.int 2)) (.app2 .mul (.int (-1)) (.pow (.var "b") (.int 2)))) (.var "x")) (.app2 .mul (.app2 .mul (.pow (.var "b") (.int 2)) (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x"))))) (.pow (.var "d") (.int (-1))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int 2) (.var "a")) (.var "b")) (.var "I1")))
  integrals := [("I1", (.app1 .tan (.app2 .add (.var "c") (.app2 .mul (.var "d") (.var "x")))))]
  independent := ["a", "b", "c", "d"]
  priority := 13141
  description := "RUBI 4.3.1.1 #5"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n:5" "4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m#5"

/-- RUBI 4.3.1.2 #20 -/
def rubi4312r20 : CRule where
  id := "integration.rubi_4_3_1_2_r20"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:20"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n")))
  result := (.app2 .mul (.app2 .mul (.pow (.app2 .mul (.var "d") (.app1 .sec (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))) (.var "m")) (.pow (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))) (.var "n"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "m") (.pow (.int 2) (.int (-1)))))))]
  independent := ["a", "b", "d", "e", "f", "m", "n"]
  conditions := [.eq (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 13142
  description := "RUBI 4.3.1.2 #20"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n:20" "4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m#20"


/-- RUBI 4.3.9 #1 -/
def rubi439r1 : CRule where
  id := "integration.rubi_4_3_9_r1"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p:1"
  shape := .antiderivRec; x := "x"
  body := (.pow (.app2 .add (.app2 .add (.var "a") (.app2 .mul (.var "b") (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.var "c") (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n2")))) (.var "p"))
  result := (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .mul (.pow (.int 4) (.var "p")) (.pow (.var "c") (.var "p"))) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.pow (.app2 .add (.var "b") (.app2 .mul (.app2 .mul (.int 2) (.var "c")) (.pow (.app1 .tan (.app2 .add (.var "d") (.app2 .mul (.var "e") (.var "x")))) (.var "n")))) (.app2 .mul (.int 2) (.var "p"))))]
  independent := ["a", "b", "c", "d", "e", "n", "n2", "p"]
  conditions := [.eq (.var "n2") (.app2 .mul (.int 2) (.var "n")),
    .eq (.app2 .add (.pow (.var "b") (.int 2)) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 4)) (.var "a")) (.var "c"))) (.int 0),
    .int (.var "p")]
  priority := 13144
  description := "RUBI 4.3.9 #1"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p:1" "4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p.m#1"


/-- RUBI 4.3.4.1 #12 -/
def rubi4341r12 : CRule where
  id := "integration.rubi_4_3_4_1_r12"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):12"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "b") (.var "f")) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.int 1) (.pow (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.int 1))) (.app2 .add (.app2 .add (.app2 .mul (.var "b") (.var "B")) (.app2 .mul (.var "a") (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C"))))) (.app2 .mul (.app2 .mul (.int (-1)) (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.var "b")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "B"))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "C")))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "e", "f", "A", "B", "C", "m"]
  conditions := [.ne (.app2 .add (.app2 .add (.app2 .mul (.var "A") (.pow (.var "b") (.int 2))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "b")) (.var "B"))) (.app2 .mul (.pow (.var "a") (.int 2)) (.var "C"))) (.int 0),
    .gt (.int (-1)) (.var "m"),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0)]
  priority := 13146
  description := "RUBI 4.3.4.1 #12"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2):12" "4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m#12"

/-- RUBI 4.3.2.1 #7 -/
def rubi4321r7 : CRule where
  id := "integration.rubi_4_3_2_1_r7"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:7"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .mul (.var "f") (.var "m")) (.int (-1)))) (.var "I1"))
  integrals := [("I1", (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.app2 .add (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.var "d"))) (.app2 .mul (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.var "a") (.var "d"))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x"))))))))]
  independent := ["a", "b", "c", "d", "e", "f", "m"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .gt (.var "m") (.int 0)]
  priority := 13147
  description := "RUBI 4.3.2.1 #7"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n:7" "4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m#7"


/-- RUBI 4.3.4.2 #14 -/
def rubi4342r14 : CRule where
  id := "integration.rubi_4_3_4_2_r14"; legacyId := some "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):14"
  shape := .antiderivRec; x := "x"
  body := (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m")) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "n"))) (.app2 .add (.app2 .add (.var "A") (.app2 .mul (.var "B") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.var "C") (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2)))))
  result := (.app2 .add (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .add (.app2 .mul (.var "A") (.pow (.var "d") (.int 2))) (.app2 .mul (.var "c") (.app2 .add (.app2 .mul (.var "c") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "d"))))) (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.var "m"))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.pow (.app2 .mul (.app2 .mul (.app2 .mul (.var "d") (.var "f")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.int 1)) (.pow (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.var "n") (.int 1))) (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2)))) (.int (-1)))) (.var "I1")))
  integrals := [("I1", (.app2 .mul (.app2 .mul (.pow (.app2 .add (.var "a") (.app2 .mul (.var "b") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "m") (.app2 .mul (.int (-1)) (.int 1)))) (.pow (.app2 .add (.var "c") (.app2 .mul (.var "d") (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .add (.var "n") (.int 1)))) (.app2 .add (.app2 .add (.app2 .add (.app2 .mul (.app2 .mul (.var "A") (.var "d")) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "d")) (.var "m")) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "c")) (.app2 .add (.var "n") (.int 1))))) (.app2 .mul (.app2 .add (.app2 .mul (.var "c") (.var "C")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "B")) (.var "d"))) (.app2 .add (.app2 .mul (.app2 .mul (.var "b") (.var "c")) (.var "m")) (.app2 .mul (.app2 .mul (.var "a") (.var "d")) (.app2 .add (.var "n") (.int 1)))))) (.app2 .mul (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "d")) (.app2 .add (.var "n") (.int 1))) (.app2 .add (.app2 .mul (.app2 .add (.var "A") (.app2 .mul (.int (-1)) (.var "C"))) (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d")))) (.app2 .mul (.var "B") (.app2 .add (.app2 .mul (.var "a") (.var "c")) (.app2 .mul (.var "b") (.var "d")))))) (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))))) (.app2 .mul (.app2 .mul (.app2 .mul (.int (-1)) (.var "b")) (.app2 .add (.app2 .mul (.app2 .mul (.var "d") (.app2 .add (.app2 .mul (.var "B") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "A")) (.var "d")))) (.app2 .add (.app2 .add (.var "m") (.var "n")) (.int 1))) (.app2 .mul (.app2 .mul (.int (-1)) (.var "C")) (.app2 .add (.app2 .mul (.pow (.var "c") (.int 2)) (.var "m")) (.app2 .mul (.app2 .mul (.int (-1)) (.pow (.var "d") (.int 2))) (.app2 .add (.var "n") (.int 1))))))) (.pow (.app1 .tan (.app2 .add (.var "e") (.app2 .mul (.var "f") (.var "x")))) (.int 2))))))]
  independent := ["a", "b", "c", "d", "e", "f", "A", "B", "C", "m", "n"]
  conditions := [.ne (.app2 .add (.app2 .mul (.var "b") (.var "c")) (.app2 .mul (.app2 .mul (.int (-1)) (.var "a")) (.var "d"))) (.int 0),
    .ne (.app2 .add (.pow (.var "a") (.int 2)) (.pow (.var "b") (.int 2))) (.int 0),
    .ne (.app2 .add (.pow (.var "c") (.int 2)) (.pow (.var "d") (.int 2))) (.int 0),
    .gt (.var "m") (.int 0),
    .gt (.int (-1)) (.var "n")]
  priority := 13149
  description := "RUBI 4.3.4.2 #14"
  provenance := migrated "rubi:4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2):14" "4 Trig functions/4.3 Tangent/4.3.4.2 (a+b tan)^m (c+d tan)^n (A+B tan+C tan^2).m#14"

/-! ## Refutations -/

theorem rubi419r29_counterexample_real : ¬ rubi419r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r29.conditions rubi419r29.body rubi419r29.result rubi419r29.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4112r33x_counterexample_real : ¬ rubi4112r33x.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4112r33x.conditions rubi4112r33x.body rubi4112r33x.result rubi4112r33x.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4112r33x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4112r33x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4112r33x.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4112r33x, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4112r33x, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4112r33x, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r1_counterexample_real : ¬ rubi4142r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r1.conditions rubi4142r1.body rubi4142r1.result rubi4142r1.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then ((-1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r14_counterexample_real : ¬ rubi4142r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r14.conditions rubi4142r14.body rubi4142r14.result rubi4142r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "d" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r31_counterexample_real : ¬ rubi4142r31.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r31.conditions rubi4142r31.body rubi4142r31.result rubi4142r31.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r31.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "c" then (4 : ℝ) else if s = "d" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r31, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r31, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r36_counterexample_real : ¬ rubi4142r36.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r36.conditions rubi4142r36.body rubi4142r36.result rubi4142r36.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "b" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r36.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "b" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r36, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r36, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r36, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r16_counterexample_real : ¬ rubi4121r16.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4121r16.conditions rubi4121r16.body rubi4121r16.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "d" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4121r16, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4121r16, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4121r23_counterexample_real : ¬ rubi4121r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r23.conditions rubi4121r23.body rubi4121r23.result rubi4121r23.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r44_counterexample_real : ¬ rubi4121r44.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r44.conditions rubi4121r44.body rubi4121r44.result rubi4121r44.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "d" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r44, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r44, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4121r44, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4121r44, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4121r56_counterexample_real : ¬ rubi4121r56.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r56.conditions rubi4121r56.body rubi4121r56.result rubi4121r56.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r56, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r56, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r56.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r56, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r56, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r56, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r89_counterexample_real : ¬ rubi4121r89.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r89.conditions rubi4121r89.body rubi4121r89.result rubi4121r89.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "m" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r89, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r89, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r89.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-1 : ℝ) else if s = "m" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r89, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r89, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r89, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4110r8_counterexample_real : ¬ rubi4110r8.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4110r8.conditions rubi4110r8.body rubi4110r8.result rubi4110r8.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "c" then (-3 : ℝ) else if s = "f" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4110r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4110r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4110r8, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4110r8, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4131r15_counterexample_real : ¬ rubi4131r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4131r15.conditions rubi4131r15.body rubi4131r15.result rubi4131r15.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (4 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4131r15.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (4 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then ((-1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4131r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4131r15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4131r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r6_counterexample_real : ¬ rubi415r6.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r6.conditions rubi415r6.body rubi415r6.result rubi415r6.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r6.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r6, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r6, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r15_counterexample_real : ¬ rubi415r15.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r15.conditions rubi415r15.body rubi415r15.result rubi415r15.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "b" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi415r15, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi415r15, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi415r24_counterexample_real : ¬ rubi415r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r24.conditions rubi415r24.body rubi415r24.result rubi415r24.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r29_counterexample_real : ¬ rubi415r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r29.conditions rubi415r29.body rubi415r29.result rubi415r29.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r34_counterexample_real : ¬ rubi415r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r34.conditions rubi415r34.body rubi415r34.result rubi415r34.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r34, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r3_counterexample_real : ¬ rubi417r3.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r3.conditions rubi417r3.body rubi417r3.result rubi417r3.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r3.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r3, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r3, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r14_counterexample_real : ¬ rubi417r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r14.conditions rubi417r14.body rubi417r14.result rubi417r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r10_counterexample_real : ¬ rubi4122r10.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r10.conditions rubi4122r10.body rubi4122r10.result rubi4122r10.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (1 : ℝ) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4122r10, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4122r10, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4122r33_counterexample_real : ¬ rubi4122r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r33.conditions rubi4122r33.body rubi4122r33.result rubi4122r33.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-2 : ℝ) else if s = "p" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((-1 : ℝ) / 2) else if s = "c" then (-2 : ℝ) else if s = "p" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r33, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r39_counterexample_real : ¬ rubi4122r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r39.conditions rubi4122r39.body rubi4122r39.result rubi4122r39.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "g" then (4 : ℝ) else if s = "p" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r39.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "g" then (4 : ℝ) else if s = "p" then (-1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r39, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4111r13_counterexample_real : ¬ rubi4111r13.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4111r13.conditions rubi4111r13.body rubi4111r13.result
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4111r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4111r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4111r13, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4111r13, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4141r2_counterexample_real : ¬ rubi4141r2.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4141r2.conditions rubi4141r2.body rubi4141r2.result
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4141r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4141r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4141r11_counterexample_real : ¬ rubi4141r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r11.conditions rubi4141r11.body rubi4141r11.result rubi4141r11.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else if s = "b" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else if s = "b" then (-2 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r5_counterexample_real : ¬ rubi416r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r5.conditions rubi416r5.body rubi416r5.result rubi416r5.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "c" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "c" then (-1 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r18_counterexample_real : ¬ rubi416r18.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r18.conditions rubi416r18.body rubi416r18.result
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r18, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r18, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r23_counterexample_real : ¬ rubi416r23.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r23.conditions rubi416r23.body rubi416r23.result rubi416r23.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r23.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then ((1 : ℝ) / 2) else if s = "b" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r23, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r23, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r28_counterexample_real : ¬ rubi416r28.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r28.conditions rubi416r28.body rubi416r28.result rubi416r28.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-3 : ℝ) else if s = "c" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r28.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-3 : ℝ) else if s = "c" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r28, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r28, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r33_counterexample_real : ¬ rubi416r33.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r33.conditions rubi416r33.body rubi416r33.result rubi416r33.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r33.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-3 : ℝ) else if s = "n" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r33, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r33, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r38_counterexample_real : ¬ rubi416r38.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r38.conditions rubi416r38.body rubi416r38.result rubi416r38.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (-1 : ℝ) else if s = "a" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r38.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (-1 : ℝ) else if s = "a" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r38, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r38, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r38, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r43_counterexample_real : ¬ rubi416r43.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r43.conditions rubi416r43.body rubi416r43.result rubi416r43.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r43, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r43, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r43.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r43, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r43, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r43, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4311r11_counterexample_real : ¬ rubi4311r11.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4311r11.conditions rubi4311r11.body rubi4311r11.result rubi4311r11.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4311r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4311r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4311r11.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4311r11, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4311r11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4311r11, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4341r4_counterexample_real : ¬ rubi4341r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4341r4.conditions rubi4341r4.body rubi4341r4.result rubi4341r4.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4341r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4341r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4341r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4341r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4341r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4341r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r20_counterexample_real : ¬ rubi4321r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r20.conditions rubi4321r20.body rubi4321r20.result rubi4321r20.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4321r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4321r20, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4321r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4321r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi419r1_counterexample_real : ¬ rubi419r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r1.conditions rubi419r1.body rubi419r1.result rubi419r1.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi419r30_counterexample_real : ¬ rubi419r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi419r30.conditions rubi419r30.body rubi419r30.result rubi419r30.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi419r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi419r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi419r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "n" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi419r30, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi419r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi419r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r2_counterexample_real : ¬ rubi4142r2.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r2.conditions rubi4142r2.body rubi4142r2.result rubi4142r2.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "f" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r2.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (-1 : ℝ) else if s = "f" then (-1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r2, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r2, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4142r19_counterexample_real : ¬ rubi4142r19.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4142r19.conditions rubi4142r19.body rubi4142r19.result rubi4142r19.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (2 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4142r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4142r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4142r19.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (2 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4142r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4142r19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4142r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r1_counterexample_real : ¬ rubi4121r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4121r1.conditions rubi4121r1.body rubi4121r1.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "d" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4121r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4121r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4121r9_counterexample_real : ¬ rubi4121r9.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4121r9.conditions rubi4121r9.body rubi4121r9.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "c" then ((-1 : ℝ) / 2) else if s = "f" then (-1 : ℝ) else if s = "n" then (-1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4121r9, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4121r9, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4121r17_counterexample_real : ¬ rubi4121r17.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r17.conditions rubi4121r17.body rubi4121r17.result rubi4121r17.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r17.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (3 : ℝ) else if s = "b" then (-3 : ℝ) else if s = "c" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r17, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r17, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r25_counterexample_real : ¬ rubi4121r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r25.conditions rubi4121r25.body rubi4121r25.result rubi4121r25.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((-1 : ℝ) / 2) else if s = "b" then ((-1 : ℝ) / 2) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r57_counterexample_real : ¬ rubi4121r57.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r57.conditions rubi4121r57.body rubi4121r57.result rubi4121r57.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r57, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r57, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r57.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "d" then (1 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r57, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r57, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r57, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4121r90_counterexample_real : ¬ rubi4121r90.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4121r90.conditions rubi4121r90.body rubi4121r90.result rubi4121r90.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4121r90, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4121r90, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4121r90.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4121r90, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4121r90, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4121r90, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4131r5_counterexample_real : ¬ rubi4131r5.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4131r5.conditions rubi4131r5.body rubi4131r5.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "A" then (1 : ℝ) else if s = "n" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4131r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4131r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4131r24_counterexample_real : ¬ rubi4131r24.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4131r24.conditions rubi4131r24.body rubi4131r24.result rubi4131r24.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4131r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4131r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4131r24.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (-1 : ℝ) else if s = "b" then (4 : ℝ) else if s = "c" then (4 : ℝ) else if s = "m" then (2 : ℝ) else if s = "n" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4131r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4131r24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4131r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi415r30_counterexample_real : ¬ rubi415r30.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi415r30.conditions rubi415r30.body rubi415r30.result rubi415r30.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi415r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi415r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi415r30.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-3 : ℝ) else if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi415r30, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi415r30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi415r30, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi417r4_counterexample_real : ¬ rubi417r4.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi417r4.conditions rubi417r4.body rubi417r4.result rubi417r4.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi417r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi417r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi417r4.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi417r4, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi417r4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi417r4, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r12_counterexample_real : ¬ rubi4122r12.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi4122r12.conditions rubi4122r12.body rubi4122r12.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "c" then (1 : ℝ) else if s = "f" then ((-1 : ℝ) / 2) else if s = "p" then (1 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi4122r12, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi4122r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi4122r25_counterexample_real : ¬ rubi4122r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r25.conditions rubi4122r25.body rubi4122r25.result rubi4122r25.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r25.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (-1 : ℝ) else if s = "b" then (1 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r34_counterexample_real : ¬ rubi4122r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r34.conditions rubi4122r34.body rubi4122r34.result rubi4122r34.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (3 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "g" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (3 : ℝ) else if s = "d" then (-3 : ℝ) else if s = "g" then (4 : ℝ) else if s = "p" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r34, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4122r78_counterexample_real : ¬ rubi4122r78.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4122r78.conditions rubi4122r78.body rubi4122r78.result rubi4122r78.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4122r78, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4122r78, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4122r78.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4122r78, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4122r78, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4122r78, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4141r12_counterexample_real : ¬ rubi4141r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4141r12.conditions rubi4141r12.body rubi4141r12.result rubi4141r12.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4141r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4141r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4141r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "b" then (-3 : ℝ) else if s = "m" then (-3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4141r12, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4141r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4141r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r1_counterexample_real : ¬ rubi416r1.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r1.conditions rubi416r1.body rubi416r1.result
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r19_counterexample_real : ¬ rubi416r19.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r19.conditions rubi416r19.body rubi416r19.result
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r19, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r19, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r24_counterexample_real : ¬ rubi416r24.Holds .real := by
  show ¬ AntiderivHoldsUnder Interp.real "x" rubi416r24.conditions rubi416r24.body rubi416r24.result
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
  refine not_antiderivHoldsUnder (fun s => if s = "A" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ?_
  · simp [rubi416r24, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · intro h
    simp [rubi416r24, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] at h

theorem rubi416r29_counterexample_real : ¬ rubi416r29.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r29.conditions rubi416r29.body rubi416r29.result rubi416r29.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-3 : ℝ) else if s = "c" then (3 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r29.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (4 : ℝ) else if s = "a" then (-3 : ℝ) else if s = "c" then (3 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r29, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r29, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r34_counterexample_real : ¬ rubi416r34.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r34.conditions rubi416r34.body rubi416r34.result rubi416r34.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "B" then (-2 : ℝ) else if s = "a" then ((1 : ℝ) / 2) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r34.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "B" then (-2 : ℝ) else if s = "a" then ((1 : ℝ) / 2) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r34, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r34, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi416r39_counterexample_real : ¬ rubi416r39.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi416r39.conditions rubi416r39.body rubi416r39.result rubi416r39.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi416r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi416r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi416r39.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "A" then (1 : ℝ) else if s = "a" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi416r39, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi416r39, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi416r39, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4331r25_counterexample_real : ¬ rubi4331r25.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4331r25.conditions rubi4331r25.body rubi4331r25.result rubi4331r25.integrals
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
  refine not_antiderivRecHolds_integrand (fun s => if s = "a" then ((1 : ℝ) / 2) else if s = "d" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4331r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4331r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num)) ⟨_, List.mem_cons_self, ?_⟩
  · simp [rubi4331r25, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp [rubi4331r25, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))

theorem rubi4311r5_counterexample_real : ¬ rubi4311r5.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4311r5.conditions rubi4311r5.body rubi4311r5.result rubi4311r5.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4311r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4311r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4311r5.integrals.lookup h).map (eval Interp.real (Function.update (fun s => 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4311r5, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4311r5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4311r5, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4312r20_counterexample_real : ¬ rubi4312r20.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4312r20.conditions rubi4312r20.body rubi4312r20.result rubi4312r20.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "m" then (2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4312r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4312r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4312r20.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "m" then (2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4312r20, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4312r20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4312r20, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi439r1_counterexample_real : ¬ rubi439r1.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi439r1.conditions rubi439r1.body rubi439r1.result rubi439r1.integrals
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
      | (refine Eventually.of_forall fun w => ?_; simp [rubi439r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi439r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi439r1.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "p" then (1 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi439r1, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi439r1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi439r1, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4341r12_counterexample_real : ¬ rubi4341r12.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4341r12.conditions rubi4341r12.body rubi4341r12.result rubi4341r12.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "C" then ((-1 : ℝ) / 2) else if s = "a" then (3 : ℝ) else if s = "m" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4341r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4341r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4341r12.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "C" then ((-1 : ℝ) / 2) else if s = "a" then (3 : ℝ) else if s = "m" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4341r12, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4341r12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4341r12, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4321r7_counterexample_real : ¬ rubi4321r7.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4321r7.conditions rubi4321r7.body rubi4321r7.result rubi4321r7.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "c" then ((-1 : ℝ) / 2) else if s = "m" then (4 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4321r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4321r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4321r7.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "b" then ((1 : ℝ) / 2) else if s = "c" then ((-1 : ℝ) / 2) else if s = "m" then (4 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4321r7, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4321r7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4321r7, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

theorem rubi4342r14_counterexample_real : ¬ rubi4342r14.Holds .real := by
  show ¬ AntiderivRecHolds Interp.real "x" rubi4342r14.conditions rubi4342r14.body rubi4342r14.result rubi4342r14.integrals
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
  refine not_antiderivRecHolds_result (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (2 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) (1 : ℝ) ?_ (by
    first
      | (refine Eventually.of_forall fun w => ?_; simp [rubi4342r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num)); done)
      | (filter_upwards [Ioo_mem_nhds (show (1 : ℝ) - 1/16 < 1 by norm_num) (show (1 : ℝ) < 1 + 1/16 by norm_num)] with w hw
         obtain ⟨h1, h2⟩ := hw
         simp [rubi4342r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12]
         repeat' constructor
         all_goals first | positivity | linarith | nlinarith [h1, h2] | (intro h; nlinarith [h1, h2]) | (exact (Real.sqrt_pos.2 (by nlinarith [h1, h2])).ne') | norm_num))
    (fun h w => w * (((rubi4342r14.integrals.lookup h).map (eval Interp.real (Function.update (fun s => if s = "a" then (1 : ℝ) else if s = "b" then (2 : ℝ) else if s = "c" then (-2 : ℝ) else if s = "m" then (4 : ℝ) else if s = "n" then (-2 : ℝ) else 0) "x" (1 : ℝ)))).getD 0)) ?_ ?_
  · simp [rubi4342r14, Cond.Holds, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12] <;> (try first | positivity | norm_num | (intro h; nlinarith) | (refine ⟨by positivity, ?_⟩; norm_num))
  · simp only [rubi4342r14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [List.lookup]
    repeat' (first | exact hasDerivAt_mul_const _ | constructor)
  · intro h
    simp [rubi4342r14, Defined, eval, Interp.real, ivm12, ivm11, ivm10, ivm9, ivm8, ivm7, ivm6, ivm5, ivm4, ivm3, ivm2, ivm1, iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, recEnv] at h

end OSR.IntegrationRec175
